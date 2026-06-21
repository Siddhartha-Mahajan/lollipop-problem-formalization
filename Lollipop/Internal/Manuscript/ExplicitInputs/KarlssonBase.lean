import Lollipop.Internal.Manuscript.ExplicitInputs.PairwiseLower

/-!
Karlsson four-base lower construction data.

The OEIS/Karlsson construction starts from four lollipops whose unordered
pair crossing table is

* one exceptional pair with `5` crossings;
* the other five inter-base pairs with `7` crossings.

This file makes that base table explicit and separates it from the later
local blow-up/perturbation certificate.  Lean proves that a construction whose
copies inherit this four-base table supplies the pairwise lower interface, and
hence the already-proved Karlsson lower polynomial.
-/

namespace Lollipop
namespace TheoremOneManuscript
namespace ExplicitInputs

universe u

open BigOperators

/-- The exact pair table for the four Karlsson base lollipops.  It is the
same symmetric table later used by the cluster blow-up: same-cluster pairs
have value `4`, the exceptional base pair `(0,1)` has value `5`, and the
remaining inter-base pairs have value `7`. -/
def karlssonBasePairCrossing (a b : Fin 4) : Rat :=
  karlssonClusterPairCrossing a b

theorem karlssonBasePairCrossing_symm (a b : Fin 4) :
    karlssonBasePairCrossing a b =
      karlssonBasePairCrossing b a :=
  karlssonClusterPairCrossing_symm a b

@[simp] theorem karlssonBasePairCrossing_same (a : Fin 4) :
    karlssonBasePairCrossing a a = 4 := by
  simp [karlssonBasePairCrossing, karlssonClusterPairCrossing]

@[simp] theorem karlssonBasePairCrossing_zero_one :
    karlssonBasePairCrossing (0 : Fin 4) (1 : Fin 4) = 5 := by
  norm_num [karlssonBasePairCrossing, karlssonClusterPairCrossing]

@[simp] theorem karlssonBasePairCrossing_zero_two :
    karlssonBasePairCrossing (0 : Fin 4) (2 : Fin 4) = 7 := by
  native_decide

@[simp] theorem karlssonBasePairCrossing_zero_three :
    karlssonBasePairCrossing (0 : Fin 4) (3 : Fin 4) = 7 := by
  native_decide

@[simp] theorem karlssonBasePairCrossing_one_two :
    karlssonBasePairCrossing (1 : Fin 4) (2 : Fin 4) = 7 := by
  native_decide

@[simp] theorem karlssonBasePairCrossing_one_three :
    karlssonBasePairCrossing (1 : Fin 4) (3 : Fin 4) = 7 := by
  native_decide

@[simp] theorem karlssonBasePairCrossing_two_three :
    karlssonBasePairCrossing (2 : Fin 4) (3 : Fin 4) = 7 := by
  native_decide

/-- The visible six-entry Karlsson base table sums to `40`. -/
theorem karlssonBasePairCrossing_six_pair_sum_eq_forty :
    karlssonBasePairCrossing (0 : Fin 4) (1 : Fin 4) +
      karlssonBasePairCrossing (0 : Fin 4) (2 : Fin 4) +
      karlssonBasePairCrossing (0 : Fin 4) (3 : Fin 4) +
      karlssonBasePairCrossing (1 : Fin 4) (2 : Fin 4) +
      karlssonBasePairCrossing (1 : Fin 4) (3 : Fin 4) +
      karlssonBasePairCrossing (2 : Fin 4) (3 : Fin 4) = 40 := by
  norm_num

/-- A concrete four-base pair table certified by the six visible unordered
Karlsson values plus symmetry.  This is closer to the manuscript table than
the theorem-facing universal `∀ a b, a ≠ b` field. -/
structure KarlssonBaseSixPairTableCertificate
    (baseCross : Fin 4 → Fin 4 → Rat) where
  symm : ∀ a b : Fin 4, baseCross a b = baseCross b a
  zero_one : baseCross (0 : Fin 4) (1 : Fin 4) = 5
  zero_two : baseCross (0 : Fin 4) (2 : Fin 4) = 7
  zero_three : baseCross (0 : Fin 4) (3 : Fin 4) = 7
  one_two : baseCross (1 : Fin 4) (2 : Fin 4) = 7
  one_three : baseCross (1 : Fin 4) (3 : Fin 4) = 7
  two_three : baseCross (2 : Fin 4) (3 : Fin 4) = 7

namespace KarlssonBaseSixPairTableCertificate

/-- The six-entry symmetric table certificate expands to the universal
distinct-label table agreement used by the lower-bound theorem stack. -/
theorem base_pair_cross_eq_karlsson
    {baseCross : Fin 4 → Fin 4 → Rat}
    (h : KarlssonBaseSixPairTableCertificate baseCross) :
    ∀ a b : Fin 4, a ≠ b →
      baseCross a b = karlssonBasePairCrossing a b := by
  intro a b hab
  fin_cases a <;> fin_cases b
  · contradiction
  · simpa [karlssonBasePairCrossing, karlssonClusterPairCrossing]
      using h.zero_one
  · simpa [karlssonBasePairCrossing, karlssonClusterPairCrossing]
      using h.zero_two
  · simpa [karlssonBasePairCrossing, karlssonClusterPairCrossing]
      using h.zero_three
  · rw [h.symm]
    simpa [karlssonBasePairCrossing, karlssonClusterPairCrossing]
      using h.zero_one
  · contradiction
  · simpa [karlssonBasePairCrossing, karlssonClusterPairCrossing]
      using h.one_two
  · simpa [karlssonBasePairCrossing, karlssonClusterPairCrossing]
      using h.one_three
  · rw [h.symm]
    simpa [karlssonBasePairCrossing, karlssonClusterPairCrossing]
      using h.zero_two
  · rw [h.symm]
    simpa [karlssonBasePairCrossing, karlssonClusterPairCrossing]
      using h.one_two
  · contradiction
  · simpa [karlssonBasePairCrossing, karlssonClusterPairCrossing]
      using h.two_three
  · rw [h.symm]
    simpa [karlssonBasePairCrossing, karlssonClusterPairCrossing]
      using h.zero_three
  · rw [h.symm]
    simpa [karlssonBasePairCrossing, karlssonClusterPairCrossing]
      using h.one_three
  · rw [h.symm]
    simpa [karlssonBasePairCrossing, karlssonClusterPairCrossing]
      using h.two_three
  · contradiction

end KarlssonBaseSixPairTableCertificate

/-- The displayed Karlsson base table itself satisfies the six-pair symmetric
table certificate. -/
def karlssonBasePairCrossing_sixPairTableCertificate :
    KarlssonBaseSixPairTableCertificate karlssonBasePairCrossing where
  symm := karlssonBasePairCrossing_symm
  zero_one := karlssonBasePairCrossing_zero_one
  zero_two := karlssonBasePairCrossing_zero_two
  zero_three := karlssonBasePairCrossing_zero_three
  one_two := karlssonBasePairCrossing_one_two
  one_three := karlssonBasePairCrossing_one_three
  two_three := karlssonBasePairCrossing_two_three

/-- The unordered-pair finite sum over the four base lollipops is `40`. -/
theorem pairSum_four_karlssonBasePairCrossing_eq_forty :
    pairSum 4 karlssonBasePairCrossing = 40 := by
  native_decide

/-- Any concrete four-base crossing table agreeing with Karlsson's table on
distinct base pairs has unordered-pair sum `40`. -/
theorem pairSum_four_eq_forty_of_base_pair_crossing_eq
    {baseCross : Fin 4 → Fin 4 → Rat}
    (hbase :
      ∀ a b : Fin 4, a ≠ b →
        baseCross a b = karlssonBasePairCrossing a b) :
    pairSum 4 baseCross = 40 := by
  rw [show pairSum 4 baseCross = pairSum 4 karlssonBasePairCrossing by
    unfold pairSum
    apply Finset.sum_congr rfl
    intro p hp
    have hp_lt : p.1 < p.2 := by
      rw [pairFinset, Finset.mem_filter] at hp
      exact hp.2
    exact hbase p.1 p.2 (ne_of_lt hp_lt)]
  exact pairSum_four_karlssonBasePairCrossing_eq_forty

/-- Pair value for two blown-up copies as inherited from a four-base table. -/
def karlssonBaseCopyPairCrossing
    (baseCross : Fin 4 → Fin 4 → Rat)
    {n : Nat} (cluster : Fin n → Fin 4) (i j : Fin n) : Rat :=
  if cluster i = cluster j then 4 else baseCross (cluster i) (cluster j)

/-- One local lower copy-pair certificate: the produced pair crossing value is
the value inherited from either the same-cluster case or the relevant
Karlsson base pair. -/
structure LocalKarlssonBaseCopyPairCrossingData
    (baseCross : Fin 4 → Fin 4 → Rat)
    {n : Nat} (cluster : Fin n → Fin 4)
    (pairCross : Fin n → Fin n → Rat)
    (i j : Fin n) (_hij : i < j) where
  pair_cross_eq :
    pairCross i j =
      karlssonBaseCopyPairCrossing baseCross cluster i j

/-- Local lower copy-pair certificates assemble into the universal pair-value
statement used by the lower-bound theorem stack. -/
theorem pair_cross_eq_base_copy_from_local
    {baseCross : Fin 4 → Fin 4 → Rat}
    {n : Nat} {cluster : Fin n → Fin 4}
    {pairCross : Fin n → Fin n → Rat}
    (loc :
      ∀ i j : Fin n, ∀ hij : i < j,
        LocalKarlssonBaseCopyPairCrossingData
          baseCross cluster pairCross i j hij) :
    ∀ i j : Fin n, ∀ _hij : i < j,
      pairCross i j =
        karlssonBaseCopyPairCrossing baseCross cluster i j := by
  intro i j hij
  exact (loc i j hij).pair_cross_eq

/-- If the four-base table is Karlsson's table on distinct base labels, then
the inherited copy-pair table is exactly the cluster table used in the lower
polynomial. -/
theorem karlssonBaseCopyPairCrossing_eq_clusterPairCrossing
    {baseCross : Fin 4 → Fin 4 → Rat}
    (hbase :
      ∀ a b : Fin 4, a ≠ b →
        baseCross a b = karlssonBasePairCrossing a b)
    {n : Nat} (cluster : Fin n → Fin 4) (i j : Fin n) :
    karlssonBaseCopyPairCrossing baseCross cluster i j =
      karlssonClusterPairCrossing (cluster i) (cluster j) := by
  unfold karlssonBaseCopyPairCrossing
  by_cases hsame : cluster i = cluster j
  · rw [hsame]
    simp [karlssonClusterPairCrossing]
  · simp [hsame, hbase (cluster i) (cluster j) hsame,
      karlssonBasePairCrossing]

/-- A lower construction certificate with the four-base Karlsson table named
separately from the local blow-up/insertion data.  The still model-specific
fields are exactly:

* the four-base arrangement and its pair table;
* the ordered incremental region certificate for the base;
* for every sorted quadruple, the locally perturbed blow-up arrangement;
* proof that every copy pair inherits either same-cluster value `4` or the
  corresponding four-base pair value;
* ordered insertion-region data for the produced arrangement.
-/
structure KarlssonBaseBlowUpIncrementalLowerData
    (P : TheoremOne.ProblemFamily.{u}) where
  base_arrangement : P.Arrangement 4
  base_pair_cross : Fin 4 → Fin 4 → Rat
  base_pair_cross_eq_karlsson :
    ∀ a b : Fin 4, a ≠ b →
      base_pair_cross a b = karlssonBasePairCrossing a b
  base_region_increment :
    OrderedIncrementalPairRegionData 4
      (P.region 4 base_arrangement) base_pair_cross
  arrangement :
    ∀ n : Nat, (q : QuadVec n) → q ∈ sortedQuadVecs n →
      P.Arrangement n
  cluster_witness :
    ∀ (n : Nat) (q : QuadVec n), q ∈ sortedQuadVecs n →
      CardinalityClusteredKarlssonTableWitness q
  pair_cross :
    ∀ n : Nat, P.Arrangement n → Fin n → Fin n → Rat
  pair_cross_eq_base_copy :
    ∀ (n : Nat) (q : QuadVec n) (hq : q ∈ sortedQuadVecs n),
      ∀ i j : Fin n, i < j →
        pair_cross n (arrangement n q hq) i j =
          karlssonBaseCopyPairCrossing base_pair_cross
            ((cluster_witness n q hq).cluster) i j
  region_increment :
    ∀ (n : Nat) (q : QuadVec n) (hq : q ∈ sortedQuadVecs n),
      OrderedIncrementalPairRegionData n
        (P.region n (arrangement n q hq))
        (pair_cross n (arrangement n q hq))

/-- The same four-base/local-blow-up lower certificate, but with the base
table supplied by the six displayed unordered inter-base values plus symmetry.
Lean expands those six fields to the universal base-table agreement. -/
structure KarlssonBaseSixPairBlowUpIncrementalLowerData
    (P : TheoremOne.ProblemFamily.{u}) where
  base_arrangement : P.Arrangement 4
  base_pair_cross : Fin 4 → Fin 4 → Rat
  base_pair_table :
    KarlssonBaseSixPairTableCertificate base_pair_cross
  base_region_increment :
    OrderedIncrementalPairRegionData 4
      (P.region 4 base_arrangement) base_pair_cross
  arrangement :
    ∀ n : Nat, (q : QuadVec n) → q ∈ sortedQuadVecs n →
      P.Arrangement n
  cluster_witness :
    ∀ (n : Nat) (q : QuadVec n), q ∈ sortedQuadVecs n →
      CardinalityClusteredKarlssonTableWitness q
  pair_cross :
    ∀ n : Nat, P.Arrangement n → Fin n → Fin n → Rat
  pair_cross_eq_base_copy :
    ∀ (n : Nat) (q : QuadVec n) (hq : q ∈ sortedQuadVecs n),
      ∀ i j : Fin n, i < j →
        pair_cross n (arrangement n q hq) i j =
          karlssonBaseCopyPairCrossing base_pair_cross
            ((cluster_witness n q hq).cluster) i j
  region_increment :
    ∀ (n : Nat) (q : QuadVec n) (hq : q ∈ sortedQuadVecs n),
      OrderedIncrementalPairRegionData n
        (P.region n (arrangement n q hq))
        (pair_cross n (arrangement n q hq))

/-- Four-base/local-blow-up lower data where each produced copy pair carries a
local certificate of its inherited base value. -/
structure KarlssonBaseSixPairLocalBlowUpIncrementalLowerData
    (P : TheoremOne.ProblemFamily.{u}) where
  base_arrangement : P.Arrangement 4
  base_pair_cross : Fin 4 → Fin 4 → Rat
  base_pair_table :
    KarlssonBaseSixPairTableCertificate base_pair_cross
  base_region_increment :
    OrderedIncrementalPairRegionData 4
      (P.region 4 base_arrangement) base_pair_cross
  arrangement :
    ∀ n : Nat, (q : QuadVec n) → q ∈ sortedQuadVecs n →
      P.Arrangement n
  cluster_witness :
    ∀ (n : Nat) (q : QuadVec n), q ∈ sortedQuadVecs n →
      CardinalityClusteredKarlssonTableWitness q
  pair_cross :
    ∀ n : Nat, P.Arrangement n → Fin n → Fin n → Rat
  local_pair_cross_eq_base_copy :
    ∀ (n : Nat) (q : QuadVec n) (hq : q ∈ sortedQuadVecs n),
      ∀ i j : Fin n, ∀ hij : i < j,
        LocalKarlssonBaseCopyPairCrossingData base_pair_cross
          ((cluster_witness n q hq).cluster)
          (pair_cross n (arrangement n q hq)) i j hij
  region_increment :
    ∀ (n : Nat) (q : QuadVec n) (hq : q ∈ sortedQuadVecs n),
      OrderedIncrementalPairRegionData n
        (P.region n (arrangement n q hq))
        (pair_cross n (arrangement n q hq))

namespace KarlssonBaseSixPairLocalBlowUpIncrementalLowerData

/-- Assemble local copy-pair lower certificates into the existing six-pair
four-base/local-blow-up lower package. -/
noncomputable def toKarlssonBaseSixPairBlowUpIncrementalLowerData
    {P : TheoremOne.ProblemFamily.{u}}
    (h : KarlssonBaseSixPairLocalBlowUpIncrementalLowerData P) :
    KarlssonBaseSixPairBlowUpIncrementalLowerData P where
  base_arrangement := h.base_arrangement
  base_pair_cross := h.base_pair_cross
  base_pair_table := h.base_pair_table
  base_region_increment := h.base_region_increment
  arrangement := h.arrangement
  cluster_witness := h.cluster_witness
  pair_cross := h.pair_cross
  pair_cross_eq_base_copy := by
    intro n q hq i j hij
    exact pair_cross_eq_base_copy_from_local
      (h.local_pair_cross_eq_base_copy n q hq) i j hij
  region_increment := h.region_increment

/-- Convert directly to the theorem-facing lower construction package. -/
noncomputable def toKarlssonBaseBlowUpIncrementalLowerData
    {P : TheoremOne.ProblemFamily.{u}}
    (h : KarlssonBaseSixPairLocalBlowUpIncrementalLowerData P) :
    KarlssonBaseBlowUpIncrementalLowerData P where
  base_arrangement := h.base_arrangement
  base_pair_cross := h.base_pair_cross
  base_pair_cross_eq_karlsson :=
    h.base_pair_table.base_pair_cross_eq_karlsson
  base_region_increment := h.base_region_increment
  arrangement := h.arrangement
  cluster_witness := h.cluster_witness
  pair_cross := h.pair_cross
  pair_cross_eq_base_copy := by
    intro n q hq i j hij
    exact pair_cross_eq_base_copy_from_local
      (h.local_pair_cross_eq_base_copy n q hq) i j hij
  region_increment := h.region_increment

end KarlssonBaseSixPairLocalBlowUpIncrementalLowerData

namespace KarlssonBaseSixPairBlowUpIncrementalLowerData

/-- Expand the six-pair base table into the existing theorem-facing lower
certificate. -/
noncomputable def toKarlssonBaseBlowUpIncrementalLowerData
    {P : TheoremOne.ProblemFamily.{u}}
    (h : KarlssonBaseSixPairBlowUpIncrementalLowerData P) :
    KarlssonBaseBlowUpIncrementalLowerData P where
  base_arrangement := h.base_arrangement
  base_pair_cross := h.base_pair_cross
  base_pair_cross_eq_karlsson :=
    h.base_pair_table.base_pair_cross_eq_karlsson
  base_region_increment := h.base_region_increment
  arrangement := h.arrangement
  cluster_witness := h.cluster_witness
  pair_cross := h.pair_cross
  pair_cross_eq_base_copy := h.pair_cross_eq_base_copy
  region_increment := h.region_increment

end KarlssonBaseSixPairBlowUpIncrementalLowerData

namespace KarlssonBaseBlowUpIncrementalLowerData

/-- The named four-base construction has `45` regions, since its pair table
sums to `40` and the incremental equation adds `4 + 1`. -/
theorem base_region_eq_forty_five
    {P : TheoremOne.ProblemFamily.{u}}
    (h : KarlssonBaseBlowUpIncrementalLowerData P) :
    P.region 4 h.base_arrangement = 45 := by
  rw [h.base_region_increment.target_eq_pairSum_add]
  rw [pairSum_four_eq_forty_of_base_pair_crossing_eq
    h.base_pair_cross_eq_karlsson]
  norm_num

/-- A four-base-plus-local-blow-up certificate implies the pairwise lower
interface.  Lean uses the base table agreement to prove every copy-pair value
is the Karlsson cluster value, then the existing pairwise layer performs the
finite summation and derives the lower polynomial. -/
noncomputable def toPairwiseCardinalityClusteredKarlssonBlowUpIncrementalLowerData
    {P : TheoremOne.ProblemFamily.{u}}
    (h : KarlssonBaseBlowUpIncrementalLowerData P) :
    PairwiseCardinalityClusteredKarlssonBlowUpIncrementalLowerData P where
  arrangement := h.arrangement
  cluster_witness := h.cluster_witness
  pair_cross := h.pair_cross
  pair_cross_eq_cluster := by
    intro n q hq i j hij
    rw [h.pair_cross_eq_base_copy n q hq i j hij]
    exact
      karlssonBaseCopyPairCrossing_eq_clusterPairCrossing
        h.base_pair_cross_eq_karlsson
        ((h.cluster_witness n q hq).cluster) i j
  region_increment := h.region_increment

/-- Forget the four-base/local-blow-up presentation after converting it to the
older named Karlsson incremental lower interface. -/
noncomputable def toKarlssonBlowUpIncrementalLowerData
    {P : TheoremOne.ProblemFamily.{u}}
    (h : KarlssonBaseBlowUpIncrementalLowerData P) :
    KarlssonBlowUpIncrementalLowerData P :=
  h.toPairwiseCardinalityClusteredKarlssonBlowUpIncrementalLowerData
    |>.toKarlssonBlowUpIncrementalLowerData

end KarlssonBaseBlowUpIncrementalLowerData

end ExplicitInputs
end TheoremOneManuscript
end Lollipop
