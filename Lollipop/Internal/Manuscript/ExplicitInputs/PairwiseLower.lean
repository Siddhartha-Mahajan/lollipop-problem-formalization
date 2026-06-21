import Lollipop.Internal.Manuscript.ExplicitInputs.PairCountedClusteredLower

/-!
Pairwise Karlsson lower construction data.

The clustered lower interfaces still let the construction supply an aggregate
crossing equality.  This file moves that boundary one step closer to the
geometry: the construction supplies a pairwise crossing table for the produced
arrangement, proves each unordered pair has the Karlsson cluster-table value,
and supplies ordered insertion-region data for that pair table.  Lean then
derives the aggregate Karlsson crossing total and the region equation.
-/

namespace Lollipop
namespace TheoremOneManuscript
namespace ExplicitInputs

universe u

/-- One local monotone lower copy-pair certificate: the produced pair
crossing value is at least the corresponding Karlsson cluster-table value.
This is the lower-bound analogue of the exact local copy-pair equality
certificate in `KarlssonBase.lean`. -/
structure LocalClusterPairLowerBoundData
    {n : Nat} (cluster : Fin n → Fin 4)
    (pairCross : Fin n → Fin n → Rat)
    (i j : Fin n) (_hij : i < j) where
  pair_cross_ge_cluster :
    karlssonClusterPairCrossing (cluster i) (cluster j) ≤
      pairCross i j

/-- Local monotone copy-pair lower certificates assemble into the universal
pairwise lower-bound statement used by the monotone lower construction
interface. -/
theorem pair_cross_ge_cluster_from_local
    {n : Nat} {cluster : Fin n → Fin 4}
    {pairCross : Fin n → Fin n → Rat}
    (loc :
      ∀ i j : Fin n, ∀ hij : i < j,
        LocalClusterPairLowerBoundData cluster pairCross i j hij) :
    ∀ i j : Fin n, ∀ _hij : i < j,
      karlssonClusterPairCrossing (cluster i) (cluster j) ≤
        pairCross i j := by
  intro i j hij
  exact (loc i j hij).pair_cross_ge_cluster

/-- Pairwise lower construction with only cardinality-clustered finite counting
data.  The aggregate crossing count is no longer an input: it is defined as
the pair sum of the supplied pairwise crossing table. -/
structure PairwiseCardinalityClusteredKarlssonBlowUpIncrementalLowerData
    (P : TheoremOne.ProblemFamily.{u}) where
  arrangement :
    ∀ n : Nat, (q : QuadVec n) → q ∈ sortedQuadVecs n →
      P.Arrangement n
  cluster_witness :
    ∀ (n : Nat) (q : QuadVec n), q ∈ sortedQuadVecs n →
      CardinalityClusteredKarlssonTableWitness q
  pair_cross :
    ∀ n : Nat, P.Arrangement n → Fin n → Fin n → Rat
  pair_cross_eq_cluster :
    ∀ (n : Nat) (q : QuadVec n) (hq : q ∈ sortedQuadVecs n),
      ∀ i j : Fin n, i < j →
        pair_cross n (arrangement n q hq) i j =
          karlssonClusterPairCrossing
            ((cluster_witness n q hq).cluster i)
            ((cluster_witness n q hq).cluster j)
  region_increment :
    ∀ (n : Nat) (q : QuadVec n) (hq : q ∈ sortedQuadVecs n),
      OrderedIncrementalPairRegionData n
        (P.region n (arrangement n q hq))
        (pair_cross n (arrangement n q hq))

namespace PairwiseCardinalityClusteredKarlssonBlowUpIncrementalLowerData

/-- The aggregate crossing count induced by a pairwise lower table. -/
def crossings
    {P : TheoremOne.ProblemFamily.{u}}
    (h : PairwiseCardinalityClusteredKarlssonBlowUpIncrementalLowerData P)
    (n : Nat) (A : P.Arrangement n) : Rat :=
  pairSum n (h.pair_cross n A)

/-- Pairwise Karlsson data imply the previous cardinality-clustered
incremental lower interface: Lean sums the pairwise table to the clustered
Karlsson pair sum and converts ordered insertion data to the ordinary
incremental region package. -/
noncomputable def toCardinalityClusteredKarlssonBlowUpIncrementalLowerData
    {P : TheoremOne.ProblemFamily.{u}}
    (h : PairwiseCardinalityClusteredKarlssonBlowUpIncrementalLowerData P) :
    CardinalityClusteredKarlssonBlowUpIncrementalLowerData P where
  crossings := h.crossings
  arrangement := h.arrangement
  cluster_witness := h.cluster_witness
  crossings_eq_clustered_pair_sum := by
    intro n q hq
    unfold crossings clusteredKarlssonPairTableCrossings pairSum
    apply Finset.sum_congr rfl
    intro p hp
    have hp_lt : p.1 < p.2 := by
      rw [pairFinset, Finset.mem_filter] at hp
      exact hp.2
    exact h.pair_cross_eq_cluster n q hq p.1 p.2 hp_lt
  region_increment := by
    intro n q hq
    exact (h.region_increment n q hq).toIncrementalPairRegionData

/-- Pairwise lower data also imply the named Karlsson blow-up lower interface
used by older theorem endpoints. -/
noncomputable def toKarlssonBlowUpIncrementalLowerData
    {P : TheoremOne.ProblemFamily.{u}}
    (h : PairwiseCardinalityClusteredKarlssonBlowUpIncrementalLowerData P) :
    KarlssonBlowUpIncrementalLowerData P :=
  h.toCardinalityClusteredKarlssonBlowUpIncrementalLowerData
    |>.toClusteredKarlssonBlowUpIncrementalLowerData
    |>.toKarlssonTableBlowUpIncrementalLowerData
    |>.toKarlssonBlowUpIncrementalLowerData

end PairwiseCardinalityClusteredKarlssonBlowUpIncrementalLowerData

/-- Monotone pairwise lower construction.  The construction supplies a
pairwise crossing table and only proves that each unordered pair has at least
the corresponding Karlsson cluster-table value.  This is enough for the lower
bound side once the ordered region recurrence is supplied. -/
structure PairwiseCardinalityClusteredKarlssonBlowUpIncrementalLowerBoundData
    (P : TheoremOne.ProblemFamily.{u}) where
  arrangement :
    ∀ n : Nat, (q : QuadVec n) → q ∈ sortedQuadVecs n →
      P.Arrangement n
  cluster_witness :
    ∀ (n : Nat) (q : QuadVec n), q ∈ sortedQuadVecs n →
      CardinalityClusteredKarlssonTableWitness q
  pair_cross :
    ∀ n : Nat, P.Arrangement n → Fin n → Fin n → Rat
  pair_cross_ge_cluster :
    ∀ (n : Nat) (q : QuadVec n) (hq : q ∈ sortedQuadVecs n),
      ∀ i j : Fin n, i < j →
        karlssonClusterPairCrossing
            ((cluster_witness n q hq).cluster i)
            ((cluster_witness n q hq).cluster j) ≤
          pair_cross n (arrangement n q hq) i j
  region_increment :
    ∀ (n : Nat) (q : QuadVec n) (hq : q ∈ sortedQuadVecs n),
      OrderedIncrementalPairRegionData n
        (P.region n (arrangement n q hq))
        (pair_cross n (arrangement n q hq))

namespace PairwiseCardinalityClusteredKarlssonBlowUpIncrementalLowerBoundData

/-- Aggregate crossing count induced by a monotone pairwise lower table. -/
def crossings
    {P : TheoremOne.ProblemFamily.{u}}
    (h : PairwiseCardinalityClusteredKarlssonBlowUpIncrementalLowerBoundData P)
    (n : Nat) (A : P.Arrangement n) : Rat :=
  pairSum n (h.pair_cross n A)

/-- The monotone pairwise table has aggregate crossing count at least the
clustered Karlsson table sum. -/
theorem clustered_pair_sum_le_crossings
    {P : TheoremOne.ProblemFamily.{u}}
    (h : PairwiseCardinalityClusteredKarlssonBlowUpIncrementalLowerBoundData P)
    (n : Nat) (q : QuadVec n) (hq : q ∈ sortedQuadVecs n) :
    clusteredKarlssonPairTableCrossings
        ((h.cluster_witness n q hq).cluster) ≤
      h.crossings n (h.arrangement n q hq) := by
  unfold clusteredKarlssonPairTableCrossings crossings pairSum
  apply Finset.sum_le_sum
  intro p hp
  have hp_lt : p.1 < p.2 := by
    rw [pairFinset, Finset.mem_filter] at hp
    exact hp.2
  exact h.pair_cross_ge_cluster n q hq p.1 p.2 hp_lt

/-- Monotone pairwise lower data imply the monotone sorted lower-realization
interface.  The proof uses finite-sum monotonicity instead of exact pair-value
classification. -/
noncomputable def toSortedLowerCrossingBoundRealizations
    {P : TheoremOne.ProblemFamily.{u}}
    (h : PairwiseCardinalityClusteredKarlssonBlowUpIncrementalLowerBoundData P) :
    SortedLowerCrossingBoundRealizations P h.crossings := by
  intro n q hq
  refine ⟨h.arrangement n q hq, ?_, ?_⟩
  · have hw :=
      (h.cluster_witness n q hq).pairSum_eq_table
    have htable :
        karlssonClusterTableCrossingsOfQuad q =
          lowerCrossingsOfQuad q :=
      karlssonClusterTableCrossingsOfQuad_eq_lowerCrossingsOfQuad q
    have hcluster :
        lowerCrossingsOfQuad q ≤ h.crossings n (h.arrangement n q hq) := by
      rw [← htable, ← hw]
      exact h.clustered_pair_sum_le_crossings n q hq
    exact hcluster
  · exact (h.region_increment n q hq).target_eq_pairSum_add

/-- Monotone pairwise lower data give lower attainment as an inequality in
the displayed candidate form. -/
theorem lower_bound_attainment_choose
    (P : TheoremOne.ProblemFamily.{u})
    (h : PairwiseCardinalityClusteredKarlssonBlowUpIncrementalLowerBoundData P) :
    ∀ n : Nat, ∃ A : P.Arrangement n,
      candidateRegionsChoose n ≤ P.region n A :=
  lower_bound_attainment_of_sortedLowerCrossingBoundRealizations_choose
    P h.toSortedLowerCrossingBoundRealizations

end PairwiseCardinalityClusteredKarlssonBlowUpIncrementalLowerBoundData

end ExplicitInputs
end TheoremOneManuscript
end Lollipop
