import Lollipop.Internal.Manuscript.ExplicitInputs.LowerTable

/-!
Clustered Karlsson lower construction data.

`LowerTable.lean` certifies a lower arrangement by the four cluster sizes
alone.  This file exposes one more layer of the blow-up construction: the
constructed `n` lollipops carry a cluster map into the four Karlsson base
lollipops, individual unordered lollipop pairs are counted by the corresponding
same-cluster/inter-cluster table value, and the individual-pair sum collapses
to the four-cluster table count.
-/

namespace Lollipop
namespace TheoremOneManuscript
namespace ExplicitInputs

universe u

/-- Symmetric pair contribution determined by two cluster labels in the
Karlsson blow-up: copies in the same cluster contribute `4`; the two
exceptional clusters `0` and `1` contribute `5`; all other inter-cluster pairs
contribute `7`. -/
def karlssonClusterPairCrossing (a b : Fin 4) : Rat :=
  if a = b then
    4
  else if ((a : Nat) = 0 ∧ (b : Nat) = 1) ∨
      ((a : Nat) = 1 ∧ (b : Nat) = 0) then
    5
  else
    7

/-- Nat-valued version of the same `4/5/7` cluster table.  This is useful for
finite lower witnesses, whose sizes are natural numbers. -/
def karlssonClusterPairCrossingNat (a b : Fin 4) : Nat :=
  if a = b then
    4
  else if ((a : Nat) = 0 ∧ (b : Nat) = 1) ∨
      ((a : Nat) = 1 ∧ (b : Nat) = 0) then
    5
  else
    7

/-- The Nat-valued cluster table coerces to the rational cluster table. -/
theorem karlssonClusterPairCrossing_eq_nat (a b : Fin 4) :
    karlssonClusterPairCrossing a b =
      (karlssonClusterPairCrossingNat a b : Rat) := by
  unfold karlssonClusterPairCrossing karlssonClusterPairCrossingNat
  by_cases hab : a = b
  · simp [hab]
  · by_cases hex :
        ((a : Nat) = 0 ∧ (b : Nat) = 1) ∨
        ((a : Nat) = 1 ∧ (b : Nat) = 0)
    · simp [hab]
    · simp [hab]

theorem karlssonClusterPairCrossing_same (a : Fin 4) :
    karlssonClusterPairCrossing a a = 4 := by
  simp [karlssonClusterPairCrossing]

theorem karlssonClusterPairCrossing_symm (a b : Fin 4) :
    karlssonClusterPairCrossing a b =
      karlssonClusterPairCrossing b a := by
  unfold karlssonClusterPairCrossing
  by_cases hab : a = b
  · subst b
    simp
  · have hba : b ≠ a := by
      intro h
      exact hab h.symm
    simp [hab, hba, and_comm, or_comm]

/-- The Nat-valued Karlsson cluster table is symmetric. -/
theorem karlssonClusterPairCrossingNat_symm (a b : Fin 4) :
    karlssonClusterPairCrossingNat a b =
      karlssonClusterPairCrossingNat b a := by
  unfold karlssonClusterPairCrossingNat
  by_cases hab : a = b
  · subst b
    simp
  · have hba : b ≠ a := by
      intro h
      exact hab h.symm
    simp [hab, hba, and_comm, or_comm]

/-- Individual-pair Karlsson table sum for a chosen cluster map on the `n`
lollipops. -/
def clusteredKarlssonPairTableCrossings
    {n : Nat} (cluster : Fin n → Fin 4) : Rat :=
  pairSum n (fun i j => karlssonClusterPairCrossing (cluster i) (cluster j))

/-- A cluster map whose fibers have the desired quadruple sizes and whose
individual-pair table sum collapses to the four-cluster Karlsson table. -/
structure ClusteredKarlssonTableWitness {n : Nat} (q : QuadVec n) where
  cluster : Fin n → Fin 4
  cluster_card_eq :
    ∀ r : Fin 4,
      (((Finset.univ : Finset (Fin n)).filter
        (fun i => cluster i = r)).card : Rat) = quadEntry q r
  pairSum_eq_table :
    clusteredKarlssonPairTableCrossings cluster =
      karlssonClusterTableCrossingsOfQuad q

/-- Named sorted Karlsson blow-up construction whose crossing count is
certified by a cluster map on the produced lollipops. -/
structure ClusteredKarlssonBlowUpLowerData
    (P : TheoremOne.ProblemFamily.{u}) where
  crossings : (n : Nat) → P.Arrangement n → Rat
  arrangement :
    ∀ n : Nat, (q : QuadVec n) → q ∈ sortedQuadVecs n →
      P.Arrangement n
  cluster_witness :
    ∀ (n : Nat) (q : QuadVec n), q ∈ sortedQuadVecs n →
      ClusteredKarlssonTableWitness q
  crossings_eq_clustered_pair_sum :
    ∀ (n : Nat) (q : QuadVec n) (hq : q ∈ sortedQuadVecs n),
      crossings n (arrangement n q hq) =
        clusteredKarlssonPairTableCrossings
          ((cluster_witness n q hq).cluster)
  regions_eq :
    ∀ (n : Nat) (q : QuadVec n) (hq : q ∈ sortedQuadVecs n),
      P.region n (arrangement n q hq) =
        crossings n (arrangement n q hq) + (n : Rat) + 1

namespace ClusteredKarlssonBlowUpLowerData

/-- Forget the individual cluster map after Lean collapses the pair sum to
the four-cluster table. -/
def toKarlssonTableBlowUpLowerData
    {P : TheoremOne.ProblemFamily.{u}}
    (h : ClusteredKarlssonBlowUpLowerData P) :
    KarlssonTableBlowUpLowerData P where
  crossings := h.crossings
  arrangement := h.arrangement
  crossings_eq_table := by
    intro n q hq
    rw [h.crossings_eq_clustered_pair_sum n q hq,
      (h.cluster_witness n q hq).pairSum_eq_table]
  regions_eq := h.regions_eq

end ClusteredKarlssonBlowUpLowerData

/-- Named sorted Karlsson blow-up construction with incremental lower region
data and a cluster map on the produced lollipops. -/
structure ClusteredKarlssonBlowUpIncrementalLowerData
    (P : TheoremOne.ProblemFamily.{u}) where
  crossings : (n : Nat) → P.Arrangement n → Rat
  arrangement :
    ∀ n : Nat, (q : QuadVec n) → q ∈ sortedQuadVecs n →
      P.Arrangement n
  cluster_witness :
    ∀ (n : Nat) (q : QuadVec n), q ∈ sortedQuadVecs n →
      ClusteredKarlssonTableWitness q
  crossings_eq_clustered_pair_sum :
    ∀ (n : Nat) (q : QuadVec n) (hq : q ∈ sortedQuadVecs n),
      crossings n (arrangement n q hq) =
        clusteredKarlssonPairTableCrossings
          ((cluster_witness n q hq).cluster)
  region_increment :
    ∀ (n : Nat) (q : QuadVec n) (hq : q ∈ sortedQuadVecs n),
      IncrementalRegionData n
        (P.region n (arrangement n q hq))
        (crossings n (arrangement n q hq))

namespace ClusteredKarlssonBlowUpIncrementalLowerData

/-- Forget incremental region data after deriving the direct region equation. -/
def toClusteredKarlssonBlowUpLowerData
    {P : TheoremOne.ProblemFamily.{u}}
    (h : ClusteredKarlssonBlowUpIncrementalLowerData P) :
    ClusteredKarlssonBlowUpLowerData P where
  crossings := h.crossings
  arrangement := h.arrangement
  cluster_witness := h.cluster_witness
  crossings_eq_clustered_pair_sum := h.crossings_eq_clustered_pair_sum
  regions_eq := by
    intro n q hq
    exact (h.region_increment n q hq).target_eq_totalCrossings_add

/-- Convert clustered incremental lower data to the four-cluster table lower
interface. -/
def toKarlssonTableBlowUpIncrementalLowerData
    {P : TheoremOne.ProblemFamily.{u}}
    (h : ClusteredKarlssonBlowUpIncrementalLowerData P) :
    KarlssonTableBlowUpIncrementalLowerData P where
  crossings := h.crossings
  arrangement := h.arrangement
  crossings_eq_table := by
    intro n q hq
    rw [h.crossings_eq_clustered_pair_sum n q hq,
      (h.cluster_witness n q hq).pairSum_eq_table]
  region_increment := h.region_increment

end ClusteredKarlssonBlowUpIncrementalLowerData

end ExplicitInputs
end TheoremOneManuscript
end Lollipop
