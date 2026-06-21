import Lollipop.Internal.Manuscript.RegionEquation
import Lollipop.Internal.Manuscript.Statement

/-!
Concrete manuscript-facing model interface.

This module is intentionally a packaging layer.  It spells out the remaining
Euclidean/model data in the terms used by the manuscript: for every
arrangement, global circle centers/radii, normalized stem directions, exact
pairwise crossing counts satisfying the canonical four-case crossing table,
and either the generic region equation in pair-sum form or a step-by-step
incremental region recurrence that implies it.  On the lower side it asks only
for sorted Karlsson blow-up crossing-count realizations.

All combinatorial, algebraic, Turan, matrix, and finite-extremum consequences
are then supplied by imported proved theorems.
-/

namespace Lollipop
namespace TheoremOneManuscript

universe u

/-- Upper Euclidean/model data for every arrangement in a problem family,
written as global extractor functions rather than existential certificates. -/
structure CanonicalExactUpperGeometryData
    (P : TheoremOne.ProblemFamily.{u}) where
  center :
    ∀ n : Nat, P.Arrangement n →
      Fin n → TheoremOneEndToEnd.PaulsenLinearAlgebra.R2
  radius :
    ∀ n : Nat, P.Arrangement n → Fin n → ℝ
  radius_pos :
    ∀ n : Nat, ∀ A : P.Arrangement n, ∀ i : Fin n,
      0 < radius n A i
  direction :
    ∀ n : Nat, P.Arrangement n → Fin n → ℝ
  direction_nonneg :
    ∀ n : Nat, ∀ A : P.Arrangement n, ∀ i : Fin n,
      0 ≤ direction n A i
  direction_lt_one :
    ∀ n : Nat, ∀ A : P.Arrangement n, ∀ i : Fin n,
      direction n A i < 1
  cross :
    ∀ n : Nat, P.Arrangement n → Fin n → Fin n → Rat
  cross_le_case :
    ∀ n : Nat, ∀ A : P.Arrangement n, ∀ i j : Fin n, i < j →
      cross n A i j ≤
        TheoremOneEndToEnd.canonicalCrossingCaseBound
          (direction n A) (center n A) (radius n A) i j
  regions_eq_pairSum :
    ∀ n : Nat, ∀ A : P.Arrangement n,
      P.region n A = pairSum n (cross n A) + (n : Rat) + 1

namespace CanonicalExactUpperGeometryData

/-- Turn global upper geometry extractors into the strongest exact-coordinate
upper certificates used by the proved theorem stack. -/
noncomputable def toUpperCertificates
    {P : TheoremOne.ProblemFamily.{u}}
    (h : CanonicalExactUpperGeometryData P) :
    TheoremOneEndToEnd.PairwiseCanonicalExactCoordinateGeometricUpperCertificates P := by
  intro n A
  exact
    ⟨{ nNat := n
       regions := P.region n A
       center := h.center n A
       radius := h.radius n A
       radius_pos := h.radius_pos n A
       direction := h.direction n A
       direction_nonneg := h.direction_nonneg n A
       direction_lt_one := h.direction_lt_one n A
       cross := h.cross n A
       cross_le_case := h.cross_le_case n A
       regions_eq_pairSum := h.regions_eq_pairSum n A },
      rfl, rfl⟩

end CanonicalExactUpperGeometryData

/-- Upper Euclidean/model data where the region equation is derived from the
canonical previous-pair insertion recurrence rather than assumed directly. -/
structure CanonicalExactUpperGeometryIncrementalData
    (P : TheoremOne.ProblemFamily.{u}) where
  center :
    ∀ n : Nat, P.Arrangement n →
      Fin n → TheoremOneEndToEnd.PaulsenLinearAlgebra.R2
  radius :
    ∀ n : Nat, P.Arrangement n → Fin n → ℝ
  radius_pos :
    ∀ n : Nat, ∀ A : P.Arrangement n, ∀ i : Fin n,
      0 < radius n A i
  direction :
    ∀ n : Nat, P.Arrangement n → Fin n → ℝ
  direction_nonneg :
    ∀ n : Nat, ∀ A : P.Arrangement n, ∀ i : Fin n,
      0 ≤ direction n A i
  direction_lt_one :
    ∀ n : Nat, ∀ A : P.Arrangement n, ∀ i : Fin n,
      direction n A i < 1
  cross :
    ∀ n : Nat, P.Arrangement n → Fin n → Fin n → Rat
  cross_le_case :
    ∀ n : Nat, ∀ A : P.Arrangement n, ∀ i j : Fin n, i < j →
      cross n A i j ≤
        TheoremOneEndToEnd.canonicalCrossingCaseBound
          (direction n A) (center n A) (radius n A) i j
  region_increment :
    ∀ n : Nat, ∀ A : P.Arrangement n,
      OrderedIncrementalPairRegionData n (P.region n A) (cross n A)

namespace CanonicalExactUpperGeometryIncrementalData

/-- The incremental upper geometry data imply the direct pair-sum region
equation expected by the existing upper-certificate stack. -/
def toCanonicalExactUpperGeometryData
    {P : TheoremOne.ProblemFamily.{u}}
    (h : CanonicalExactUpperGeometryIncrementalData P) :
    CanonicalExactUpperGeometryData P where
  center := h.center
  radius := h.radius
  radius_pos := h.radius_pos
  direction := h.direction
  direction_nonneg := h.direction_nonneg
  direction_lt_one := h.direction_lt_one
  cross := h.cross
  cross_le_case := h.cross_le_case
  regions_eq_pairSum := by
    intro n A
    exact OrderedIncrementalPairRegionData.target_eq_pairSum_add
      (h.region_increment n A)

/-- Turn incremental upper geometry data into the exact-coordinate upper
certificates used by the theorem stack. -/
noncomputable def toUpperCertificates
    {P : TheoremOne.ProblemFamily.{u}}
    (h : CanonicalExactUpperGeometryIncrementalData P) :
    TheoremOneEndToEnd.PairwiseCanonicalExactCoordinateGeometricUpperCertificates P :=
  h.toCanonicalExactUpperGeometryData.toUpperCertificates

end CanonicalExactUpperGeometryIncrementalData

/-- Sorted Karlsson lower data for a problem family. -/
structure SortedKarlssonLowerData
    (P : TheoremOne.ProblemFamily.{u}) where
  crossings : (n : Nat) → P.Arrangement n → Rat
  realizations : SortedLowerCrossingRealizations P crossings

/-- Sorted Karlsson lower data where the lower region equation is also
supplied by incremental insertion data. -/
structure SortedKarlssonIncrementalLowerData
    (P : TheoremOne.ProblemFamily.{u}) where
  crossings : (n : Nat) → P.Arrangement n → Rat
  realizations : SortedLowerIncrementalCrossingRealizations P crossings

namespace SortedKarlssonIncrementalLowerData

/-- Forget the incremental lower proof details after deriving
`regions = crossings + n + 1`. -/
def toSortedKarlssonLowerData
    {P : TheoremOne.ProblemFamily.{u}}
    (h : SortedKarlssonIncrementalLowerData P) :
    SortedKarlssonLowerData P where
  crossings := h.crossings
  realizations :=
    sortedLowerCrossingRealizations_of_incremental
      P (crossings := h.crossings) h.realizations

end SortedKarlssonIncrementalLowerData

/-- The remaining manuscript-model obligations after all internal proof
layers have been discharged. -/
structure ConcreteModelSubtheorems
    (P : TheoremOne.ProblemFamily.{u}) where
  upper_geometry : CanonicalExactUpperGeometryData P
  lower_karlsson : SortedKarlssonLowerData P

namespace ConcreteModelSubtheorems

/-- Convert the explicit manuscript-model obligations into the concise
subtheorem package used by the manuscript-facing final theorem. -/
noncomputable def toCanonicalExactCoordinateGeometricCrossingModelSubtheorems
    {P : TheoremOne.ProblemFamily.{u}}
    (h : ConcreteModelSubtheorems P) :
    CanonicalExactCoordinateGeometricCrossingModelSubtheorems P where
  upper_certificates := h.upper_geometry.toUpperCertificates
  lower_sorted_crossing_realizations :=
    ⟨h.lower_karlsson.crossings, h.lower_karlsson.realizations⟩

end ConcreteModelSubtheorems

/-- Concrete manuscript-model obligations with the upper region equation
proved from canonical previous-pair insertion data. -/
structure ConcreteIncrementalModelSubtheorems
    (P : TheoremOne.ProblemFamily.{u}) where
  upper_geometry : CanonicalExactUpperGeometryIncrementalData P
  lower_karlsson : SortedKarlssonLowerData P

/-- Concrete manuscript-model obligations where both upper and lower region
equations are supplied by incremental insertion data. -/
structure ConcreteFullyIncrementalModelSubtheorems
    (P : TheoremOne.ProblemFamily.{u}) where
  upper_geometry : CanonicalExactUpperGeometryIncrementalData P
  lower_karlsson : SortedKarlssonIncrementalLowerData P

namespace ConcreteIncrementalModelSubtheorems

/-- Forget the incremental proof details after deriving the pair-sum region
equation. -/
def toConcreteModelSubtheorems
    {P : TheoremOne.ProblemFamily.{u}}
    (h : ConcreteIncrementalModelSubtheorems P) :
    ConcreteModelSubtheorems P where
  upper_geometry := h.upper_geometry.toCanonicalExactUpperGeometryData
  lower_karlsson := h.lower_karlsson

end ConcreteIncrementalModelSubtheorems

namespace ConcreteFullyIncrementalModelSubtheorems

/-- Forget lower incremental proof details after deriving the ordinary sorted
Karlsson lower interface. -/
def toConcreteIncrementalModelSubtheorems
    {P : TheoremOne.ProblemFamily.{u}}
    (h : ConcreteFullyIncrementalModelSubtheorems P) :
    ConcreteIncrementalModelSubtheorems P where
  upper_geometry := h.upper_geometry
  lower_karlsson := h.lower_karlsson.toSortedKarlssonLowerData

end ConcreteFullyIncrementalModelSubtheorems

/-- Maximum-form Theorem 1 from the explicit concrete manuscript model
obligations. -/
theorem theorem_one_statement_proven_from_concrete_model
    (P : TheoremOne.ProblemFamily.{u})
    (h : ConcreteModelSubtheorems P) :
    TheoremOneFinal.TheoremOneStatement P := by
  exact
    theorem_one_statement_proven_from_canonical_exact_coordinate_geometric_crossing_certificates
      P h.toCanonicalExactCoordinateGeometricCrossingModelSubtheorems

/-- Maximum-form Theorem 1 from concrete manuscript obligations whose region
equation is supplied by incremental insertion data. -/
theorem theorem_one_statement_proven_from_incremental_concrete_model
    (P : TheoremOne.ProblemFamily.{u})
    (h : ConcreteIncrementalModelSubtheorems P) :
    TheoremOneFinal.TheoremOneStatement P := by
  exact theorem_one_statement_proven_from_concrete_model
    P h.toConcreteModelSubtheorems

/-- Maximum-form Theorem 1 from fully incremental concrete manuscript
obligations. -/
theorem theorem_one_statement_proven_from_fully_incremental_concrete_model
    (P : TheoremOne.ProblemFamily.{u})
    (h : ConcreteFullyIncrementalModelSubtheorems P) :
    TheoremOneFinal.TheoremOneStatement P := by
  exact theorem_one_statement_proven_from_incremental_concrete_model
    P h.toConcreteIncrementalModelSubtheorems

/-- Concrete manuscript-model obligations for a family with a named maximum
count function. -/
def MaxConcreteModelSubtheorems
    (P : TheoremOne.MaxProblemFamily.{u}) : Type u :=
  ConcreteModelSubtheorems P.toProblemFamily

/-- Incremental concrete manuscript-model obligations for a family with a
named maximum count function. -/
def MaxConcreteIncrementalModelSubtheorems
    (P : TheoremOne.MaxProblemFamily.{u}) : Type u :=
  ConcreteIncrementalModelSubtheorems P.toProblemFamily

/-- Fully incremental concrete manuscript-model obligations for a family with
a named maximum count function. -/
def MaxConcreteFullyIncrementalModelSubtheorems
    (P : TheoremOne.MaxProblemFamily.{u}) : Type u :=
  ConcreteFullyIncrementalModelSubtheorems P.toProblemFamily

/-- Formula-form Theorem 1 from the explicit concrete manuscript model
obligations. -/
theorem theorem_one_formula_statement_proven_from_concrete_model
    (P : TheoremOne.MaxProblemFamily.{u})
    (h : MaxConcreteModelSubtheorems P) :
    TheoremOneFormulaStatement P := by
  exact
    theorem_one_formula_statement_proven_from_manuscript_canonical_exact_coordinate_geometric_crossing_certificates
      P h.toCanonicalExactCoordinateGeometricCrossingModelSubtheorems

/-- Formula-form Theorem 1 from incremental concrete manuscript obligations. -/
theorem theorem_one_formula_statement_proven_from_incremental_concrete_model
    (P : TheoremOne.MaxProblemFamily.{u})
    (h : MaxConcreteIncrementalModelSubtheorems P) :
    TheoremOneFormulaStatement P := by
  exact theorem_one_formula_statement_proven_from_concrete_model
    P h.toConcreteModelSubtheorems

/-- Formula-form Theorem 1 from fully incremental concrete manuscript
obligations. -/
theorem theorem_one_formula_statement_proven_from_fully_incremental_concrete_model
    (P : TheoremOne.MaxProblemFamily.{u})
    (h : MaxConcreteFullyIncrementalModelSubtheorems P) :
    TheoremOneFormulaStatement P := by
  exact theorem_one_formula_statement_proven_from_incremental_concrete_model
    P h.toConcreteIncrementalModelSubtheorems

/-- Single-size displayed formula from the explicit concrete manuscript model
obligations. -/
theorem theorem_one_formula_at_proven_from_concrete_model
    (P : TheoremOne.MaxProblemFamily.{u})
    (h : MaxConcreteModelSubtheorems P)
    (n : Nat) :
    P.aLop n =
      4 * ((n.choose 2 : Nat) : Rat) + manuscriptS n + (n : Rat) + 1 := by
  exact theorem_one_formula_statement_proven_from_concrete_model P h n

/-- Single-size displayed formula from incremental concrete manuscript
obligations. -/
theorem theorem_one_formula_at_proven_from_incremental_concrete_model
    (P : TheoremOne.MaxProblemFamily.{u})
    (h : MaxConcreteIncrementalModelSubtheorems P)
    (n : Nat) :
    P.aLop n =
      4 * ((n.choose 2 : Nat) : Rat) + manuscriptS n + (n : Rat) + 1 := by
  exact theorem_one_formula_statement_proven_from_incremental_concrete_model P h n

/-- Single-size displayed formula from fully incremental concrete manuscript
obligations. -/
theorem theorem_one_formula_at_proven_from_fully_incremental_concrete_model
    (P : TheoremOne.MaxProblemFamily.{u})
    (h : MaxConcreteFullyIncrementalModelSubtheorems P)
    (n : Nat) :
    P.aLop n =
      4 * ((n.choose 2 : Nat) : Rat) + manuscriptS n + (n : Rat) + 1 := by
  exact theorem_one_formula_statement_proven_from_fully_incremental_concrete_model P h n

end TheoremOneManuscript
end Lollipop
