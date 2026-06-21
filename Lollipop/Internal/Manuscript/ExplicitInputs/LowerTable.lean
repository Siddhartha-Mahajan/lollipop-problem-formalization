import Lollipop.Internal.Manuscript.ExplicitInputs.Lower

/-!
Table-shaped Karlsson lower construction data.

`ExplicitInputs/Lower.lean` asks the lower construction to prove directly
that its crossing count is `lowerCrossingsOfQuad q`.  This file splits that
obligation into the manuscript's four-cluster crossing table: intra-cluster
pairs contribute `4`, the exceptional inter-cluster pair `(0,1)` contributes
`5`, and the other five inter-cluster pairs contribute `7`.  Lean proves that
the finite table sum is exactly the old `lowerCrossingsOfQuad` formula.
-/

namespace Lollipop
namespace TheoremOneManuscript
namespace ExplicitInputs

universe u

/-- The inter-cluster part of Karlsson's four-cluster lower crossing table.
This function is intended for ordered pairs `i < j`; on that support the only
exceptional pair is `(0,1)`. -/
def karlssonInterClusterCrossing (i j : Fin 4) : Rat :=
  if (i : Nat) = 0 ∧ (j : Nat) = 1 then 5 else 7

/-- Karlsson's four-cluster crossing count as a finite table sum over the
four cluster sizes. -/
def karlssonClusterTableCrossingsQ (m : Fin 4 → Rat) : Rat :=
  (∑ i : Fin 4, 4 * binomTwoQ (m i)) +
    karlssonInterClusterCrossing 0 1 * m 0 * m 1 +
    karlssonInterClusterCrossing 0 2 * m 0 * m 2 +
    karlssonInterClusterCrossing 0 3 * m 0 * m 3 +
    karlssonInterClusterCrossing 1 2 * m 1 * m 2 +
    karlssonInterClusterCrossing 1 3 * m 1 * m 3 +
    karlssonInterClusterCrossing 2 3 * m 2 * m 3

/-- The finite table-sum form is exactly the lower crossing polynomial used
throughout the theorem stack. -/
theorem karlssonClusterTableCrossingsQ_eq_lowerCrossingsQ
    (m : Fin 4 → Rat) :
    karlssonClusterTableCrossingsQ m =
      lowerCrossingsQ (m 0) (m 1) (m 2) (m 3) := by
  unfold karlssonClusterTableCrossingsQ lowerCrossingsQ
    karlssonInterClusterCrossing binomTwoQ
  norm_num [Fin.sum_univ_four]
  ring

/-- Karlsson's four-cluster table count for a bounded integer quadruple. -/
def karlssonClusterTableCrossingsOfQuad {n : Nat} (q : QuadVec n) : Rat :=
  karlssonClusterTableCrossingsQ (fun i => quadEntry q i)

/-- The table count attached to a quadruple is the existing lower crossing
count attached to that quadruple. -/
theorem karlssonClusterTableCrossingsOfQuad_eq_lowerCrossingsOfQuad
    {n : Nat} (q : QuadVec n) :
    karlssonClusterTableCrossingsOfQuad q = lowerCrossingsOfQuad q := by
  unfold karlssonClusterTableCrossingsOfQuad lowerCrossingsOfQuad
  exact karlssonClusterTableCrossingsQ_eq_lowerCrossingsQ
    (fun i => quadEntry q i)

/-- Named sorted Karlsson blow-up construction whose crossing count is
certified by the four-cluster table sum. -/
structure KarlssonTableBlowUpLowerData
    (P : TheoremOne.ProblemFamily.{u}) where
  crossings : (n : Nat) → P.Arrangement n → Rat
  arrangement :
    ∀ n : Nat, (q : QuadVec n) → q ∈ sortedQuadVecs n →
      P.Arrangement n
  crossings_eq_table :
    ∀ (n : Nat) (q : QuadVec n) (hq : q ∈ sortedQuadVecs n),
      crossings n (arrangement n q hq) =
        karlssonClusterTableCrossingsOfQuad q
  regions_eq :
    ∀ (n : Nat) (q : QuadVec n) (hq : q ∈ sortedQuadVecs n),
      P.region n (arrangement n q hq) =
        crossings n (arrangement n q hq) + (n : Rat) + 1

namespace KarlssonTableBlowUpLowerData

/-- Forget the table presentation after Lean has rewritten it to
`lowerCrossingsOfQuad`. -/
def toKarlssonBlowUpLowerData
    {P : TheoremOne.ProblemFamily.{u}}
    (h : KarlssonTableBlowUpLowerData P) :
    KarlssonBlowUpLowerData P where
  crossings := h.crossings
  arrangement := h.arrangement
  crossings_eq_lower := by
    intro n q hq
    rw [h.crossings_eq_table n q hq,
      karlssonClusterTableCrossingsOfQuad_eq_lowerCrossingsOfQuad]
  regions_eq := h.regions_eq

/-- Table-shaped lower data imply the sorted lower-realization package. -/
def toSortedKarlssonLowerData
    {P : TheoremOne.ProblemFamily.{u}}
    (h : KarlssonTableBlowUpLowerData P) :
    SortedKarlssonLowerData P :=
  h.toKarlssonBlowUpLowerData.toSortedKarlssonLowerData

end KarlssonTableBlowUpLowerData

/-- Named sorted Karlsson blow-up construction with the lower region equation
proved from incremental insertion data and the crossing count certified by
the four-cluster table sum. -/
structure KarlssonTableBlowUpIncrementalLowerData
    (P : TheoremOne.ProblemFamily.{u}) where
  crossings : (n : Nat) → P.Arrangement n → Rat
  arrangement :
    ∀ n : Nat, (q : QuadVec n) → q ∈ sortedQuadVecs n →
      P.Arrangement n
  crossings_eq_table :
    ∀ (n : Nat) (q : QuadVec n) (hq : q ∈ sortedQuadVecs n),
      crossings n (arrangement n q hq) =
        karlssonClusterTableCrossingsOfQuad q
  region_increment :
    ∀ (n : Nat) (q : QuadVec n) (hq : q ∈ sortedQuadVecs n),
      IncrementalRegionData n
        (P.region n (arrangement n q hq))
        (crossings n (arrangement n q hq))

namespace KarlssonTableBlowUpIncrementalLowerData

/-- Forget the incremental region proof after deriving the direct region
equation, retaining the table-shaped crossing certification. -/
def toKarlssonTableBlowUpLowerData
    {P : TheoremOne.ProblemFamily.{u}}
    (h : KarlssonTableBlowUpIncrementalLowerData P) :
    KarlssonTableBlowUpLowerData P where
  crossings := h.crossings
  arrangement := h.arrangement
  crossings_eq_table := h.crossings_eq_table
  regions_eq := by
    intro n q hq
    exact (h.region_increment n q hq).target_eq_totalCrossings_add

/-- Convert the table-shaped incremental lower construction to the existing
named blow-up construction interface. -/
def toKarlssonBlowUpIncrementalLowerData
    {P : TheoremOne.ProblemFamily.{u}}
    (h : KarlssonTableBlowUpIncrementalLowerData P) :
    KarlssonBlowUpIncrementalLowerData P where
  crossings := h.crossings
  arrangement := h.arrangement
  crossings_eq_lower := by
    intro n q hq
    rw [h.crossings_eq_table n q hq,
      karlssonClusterTableCrossingsOfQuad_eq_lowerCrossingsOfQuad]
  region_increment := h.region_increment

/-- Table-shaped incremental lower data imply the existing incremental sorted
lower-realization package. -/
def toSortedKarlssonIncrementalLowerData
    {P : TheoremOne.ProblemFamily.{u}}
    (h : KarlssonTableBlowUpIncrementalLowerData P) :
    SortedKarlssonIncrementalLowerData P :=
  h.toKarlssonBlowUpIncrementalLowerData.toSortedKarlssonIncrementalLowerData

end KarlssonTableBlowUpIncrementalLowerData

end ExplicitInputs
end TheoremOneManuscript
end Lollipop
