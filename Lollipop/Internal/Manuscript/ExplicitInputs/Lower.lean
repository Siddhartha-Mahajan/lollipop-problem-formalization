import Lollipop.Internal.Manuscript.ConcreteModel

/-!
Explicit lower-construction inputs for the manuscript version of Theorem 1.

The older sorted Karlsson interfaces only ask for an arrangement realizing
each sorted quadruple.  This file exposes the more construction-shaped
interface used in the manuscript: for every sorted quadruple, a named
Karlsson blow-up arrangement is produced, its crossing count is the lower
quadruple count, and its region equation is either supplied directly or
derived from incremental insertion data.
-/

namespace Lollipop
namespace TheoremOneManuscript
namespace ExplicitInputs

universe u

/-- A named sorted Karlsson blow-up construction for every sorted quadruple,
with the lower region equation supplied directly. -/
structure KarlssonBlowUpLowerData
    (P : TheoremOne.ProblemFamily.{u}) where
  crossings : (n : Nat) → P.Arrangement n → Rat
  arrangement :
    ∀ n : Nat, (q : QuadVec n) → q ∈ sortedQuadVecs n →
      P.Arrangement n
  crossings_eq_lower :
    ∀ (n : Nat) (q : QuadVec n) (hq : q ∈ sortedQuadVecs n),
      crossings n (arrangement n q hq) = lowerCrossingsOfQuad q
  regions_eq :
    ∀ (n : Nat) (q : QuadVec n) (hq : q ∈ sortedQuadVecs n),
      P.region n (arrangement n q hq) =
        crossings n (arrangement n q hq) + (n : Rat) + 1

namespace KarlssonBlowUpLowerData

/-- A named Karlsson blow-up construction implies the older existential
sorted lower-realization interface. -/
def toSortedKarlssonLowerData
    {P : TheoremOne.ProblemFamily.{u}}
    (h : KarlssonBlowUpLowerData P) :
    SortedKarlssonLowerData P where
  crossings := h.crossings
  realizations := by
    intro n q hq
    exact ⟨h.arrangement n q hq, h.crossings_eq_lower n q hq,
      h.regions_eq n q hq⟩

end KarlssonBlowUpLowerData

/-- A named sorted Karlsson blow-up construction where the lower region
equation is proved from incremental insertion data. -/
structure KarlssonBlowUpIncrementalLowerData
    (P : TheoremOne.ProblemFamily.{u}) where
  crossings : (n : Nat) → P.Arrangement n → Rat
  arrangement :
    ∀ n : Nat, (q : QuadVec n) → q ∈ sortedQuadVecs n →
      P.Arrangement n
  crossings_eq_lower :
    ∀ (n : Nat) (q : QuadVec n) (hq : q ∈ sortedQuadVecs n),
      crossings n (arrangement n q hq) = lowerCrossingsOfQuad q
  region_increment :
    ∀ (n : Nat) (q : QuadVec n) (hq : q ∈ sortedQuadVecs n),
      IncrementalRegionData n
        (P.region n (arrangement n q hq))
        (crossings n (arrangement n q hq))

namespace KarlssonBlowUpIncrementalLowerData

/-- Forget the step-by-step lower construction after deriving the direct
lower region equation. -/
def toKarlssonBlowUpLowerData
    {P : TheoremOne.ProblemFamily.{u}}
    (h : KarlssonBlowUpIncrementalLowerData P) :
    KarlssonBlowUpLowerData P where
  crossings := h.crossings
  arrangement := h.arrangement
  crossings_eq_lower := h.crossings_eq_lower
  regions_eq := by
    intro n q hq
    exact (h.region_increment n q hq).target_eq_totalCrossings_add

/-- A named incremental Karlsson blow-up construction implies the older
existential incremental sorted lower-realization interface. -/
def toSortedKarlssonIncrementalLowerData
    {P : TheoremOne.ProblemFamily.{u}}
    (h : KarlssonBlowUpIncrementalLowerData P) :
    SortedKarlssonIncrementalLowerData P where
  crossings := h.crossings
  realizations := by
    intro n q hq
    exact ⟨h.arrangement n q hq, h.region_increment n q hq,
      h.crossings_eq_lower n q hq⟩

/-- A named incremental Karlsson blow-up construction also implies the direct
sorted lower-realization interface. -/
def toSortedKarlssonLowerData
    {P : TheoremOne.ProblemFamily.{u}}
    (h : KarlssonBlowUpIncrementalLowerData P) :
    SortedKarlssonLowerData P :=
  h.toKarlssonBlowUpLowerData.toSortedKarlssonLowerData

end KarlssonBlowUpIncrementalLowerData

/-- Direct named Karlsson blow-up data give lower attainment of the
Theorem 1 candidate. -/
theorem lower_attainment_of_karlssonBlowUpLowerData_choose
    (P : TheoremOne.ProblemFamily.{u})
    (h : KarlssonBlowUpLowerData P) :
    ∀ n : Nat, ∃ A : P.Arrangement n,
      P.region n A = candidateRegionsChoose n := by
  exact
    lower_attainment_of_sortedLowerCrossingRealizations_choose
      P (crossings := h.crossings) h.toSortedKarlssonLowerData.realizations

/-- Incremental named Karlsson blow-up data give lower attainment of the
Theorem 1 candidate. -/
theorem lower_attainment_of_karlssonBlowUpIncrementalLowerData_choose
    (P : TheoremOne.ProblemFamily.{u})
    (h : KarlssonBlowUpIncrementalLowerData P) :
    ∀ n : Nat, ∃ A : P.Arrangement n,
      P.region n A = candidateRegionsChoose n := by
  exact
    lower_attainment_of_sortedLowerIncrementalCrossingRealizations_choose
      P (crossings := h.crossings)
      h.toSortedKarlssonIncrementalLowerData.realizations

end ExplicitInputs
end TheoremOneManuscript
end Lollipop
