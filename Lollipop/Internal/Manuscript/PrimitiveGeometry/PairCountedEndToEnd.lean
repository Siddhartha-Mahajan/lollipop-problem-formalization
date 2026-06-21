import Lollipop.Internal.Manuscript.ExplicitInputs.PairCountedEndToEnd
import Lollipop.Internal.Manuscript.PrimitiveGeometry.EndToEnd

/-!
Primitive-geometry Theorem 1 endpoints with pair-counted clustered lower data.

This keeps the primitive coordinate upper packages separate from the new lower
pair-count layer.  The proof is by conversion to the already checked clustered
primitive endpoints.
-/

namespace Lollipop
namespace TheoremOneManuscript
namespace PrimitiveGeometry

universe u

/-- Primitive coordinate upper data plus a pair-counted clustered Karlsson
blow-up lower construction. -/
structure PrimitiveGeometryAndPairCountedClusteredBlowUpSubtheorems
    (P : TheoremOne.ProblemFamily.{u}) where
  upper_geometry : PrimitiveExactUpperGeometryData P
  lower_karlsson :
    ExplicitInputs.PairCountedClusteredKarlssonBlowUpIncrementalLowerData P

namespace PrimitiveGeometryAndPairCountedClusteredBlowUpSubtheorems

def toPrimitiveGeometryAndClusteredBlowUpSubtheorems
    {P : TheoremOne.ProblemFamily.{u}}
    (h : PrimitiveGeometryAndPairCountedClusteredBlowUpSubtheorems P) :
    PrimitiveGeometryAndClusteredBlowUpSubtheorems P where
  upper_geometry := h.upper_geometry
  lower_karlsson :=
    h.lower_karlsson.toClusteredKarlssonBlowUpIncrementalLowerData

end PrimitiveGeometryAndPairCountedClusteredBlowUpSubtheorems

/-- Carrier-certified primitive coordinate upper data plus a pair-counted
clustered Karlsson blow-up lower construction. -/
structure PrimitiveCarrierGeometryAndPairCountedClusteredBlowUpSubtheorems
    (P : TheoremOne.ProblemFamily.{u}) where
  upper_geometry : PrimitiveCarrierCertifiedExactUpperGeometryData P
  lower_karlsson :
    ExplicitInputs.PairCountedClusteredKarlssonBlowUpIncrementalLowerData P

namespace PrimitiveCarrierGeometryAndPairCountedClusteredBlowUpSubtheorems

def toPrimitiveCarrierGeometryAndClusteredBlowUpSubtheorems
    {P : TheoremOne.ProblemFamily.{u}}
    (h : PrimitiveCarrierGeometryAndPairCountedClusteredBlowUpSubtheorems P) :
    PrimitiveCarrierGeometryAndClusteredBlowUpSubtheorems P where
  upper_geometry := h.upper_geometry
  lower_karlsson :=
    h.lower_karlsson.toClusteredKarlssonBlowUpIncrementalLowerData

end PrimitiveCarrierGeometryAndPairCountedClusteredBlowUpSubtheorems

/-- Primitive coordinate upper data plus a fiber-counted clustered Karlsson
blow-up lower construction. -/
structure PrimitiveGeometryAndFiberCountedClusteredBlowUpSubtheorems
    (P : TheoremOne.ProblemFamily.{u}) where
  upper_geometry : PrimitiveExactUpperGeometryData P
  lower_karlsson :
    ExplicitInputs.FiberCountedClusteredKarlssonBlowUpIncrementalLowerData P

namespace PrimitiveGeometryAndFiberCountedClusteredBlowUpSubtheorems

def toPrimitiveGeometryAndPairCountedClusteredBlowUpSubtheorems
    {P : TheoremOne.ProblemFamily.{u}}
    (h : PrimitiveGeometryAndFiberCountedClusteredBlowUpSubtheorems P) :
    PrimitiveGeometryAndPairCountedClusteredBlowUpSubtheorems P where
  upper_geometry := h.upper_geometry
  lower_karlsson :=
    h.lower_karlsson.toPairCountedClusteredKarlssonBlowUpIncrementalLowerData

end PrimitiveGeometryAndFiberCountedClusteredBlowUpSubtheorems

/-- Carrier-certified primitive coordinate upper data plus a fiber-counted
clustered Karlsson blow-up lower construction. -/
structure PrimitiveCarrierGeometryAndFiberCountedClusteredBlowUpSubtheorems
    (P : TheoremOne.ProblemFamily.{u}) where
  upper_geometry : PrimitiveCarrierCertifiedExactUpperGeometryData P
  lower_karlsson :
    ExplicitInputs.FiberCountedClusteredKarlssonBlowUpIncrementalLowerData P

namespace PrimitiveCarrierGeometryAndFiberCountedClusteredBlowUpSubtheorems

def toPrimitiveCarrierGeometryAndPairCountedClusteredBlowUpSubtheorems
    {P : TheoremOne.ProblemFamily.{u}}
    (h : PrimitiveCarrierGeometryAndFiberCountedClusteredBlowUpSubtheorems P) :
    PrimitiveCarrierGeometryAndPairCountedClusteredBlowUpSubtheorems P where
  upper_geometry := h.upper_geometry
  lower_karlsson :=
    h.lower_karlsson.toPairCountedClusteredKarlssonBlowUpIncrementalLowerData

end PrimitiveCarrierGeometryAndFiberCountedClusteredBlowUpSubtheorems

/-- Primitive coordinate upper data plus a cardinality-only clustered
Karlsson blow-up lower construction. -/
structure PrimitiveGeometryAndCardinalityClusteredBlowUpSubtheorems
    (P : TheoremOne.ProblemFamily.{u}) where
  upper_geometry : PrimitiveExactUpperGeometryData P
  lower_karlsson :
    ExplicitInputs.CardinalityClusteredKarlssonBlowUpIncrementalLowerData P

namespace PrimitiveGeometryAndCardinalityClusteredBlowUpSubtheorems

def toPrimitiveGeometryAndFiberCountedClusteredBlowUpSubtheorems
    {P : TheoremOne.ProblemFamily.{u}}
    (h : PrimitiveGeometryAndCardinalityClusteredBlowUpSubtheorems P) :
    PrimitiveGeometryAndFiberCountedClusteredBlowUpSubtheorems P where
  upper_geometry := h.upper_geometry
  lower_karlsson :=
    h.lower_karlsson.toFiberCountedClusteredKarlssonBlowUpIncrementalLowerData

end PrimitiveGeometryAndCardinalityClusteredBlowUpSubtheorems

/-- Carrier-certified primitive coordinate upper data plus a cardinality-only
clustered Karlsson blow-up lower construction. -/
structure PrimitiveCarrierGeometryAndCardinalityClusteredBlowUpSubtheorems
    (P : TheoremOne.ProblemFamily.{u}) where
  upper_geometry : PrimitiveCarrierCertifiedExactUpperGeometryData P
  lower_karlsson :
    ExplicitInputs.CardinalityClusteredKarlssonBlowUpIncrementalLowerData P

namespace PrimitiveCarrierGeometryAndCardinalityClusteredBlowUpSubtheorems

def toPrimitiveCarrierGeometryAndFiberCountedClusteredBlowUpSubtheorems
    {P : TheoremOne.ProblemFamily.{u}}
    (h : PrimitiveCarrierGeometryAndCardinalityClusteredBlowUpSubtheorems P) :
    PrimitiveCarrierGeometryAndFiberCountedClusteredBlowUpSubtheorems P where
  upper_geometry := h.upper_geometry
  lower_karlsson :=
    h.lower_karlsson.toFiberCountedClusteredKarlssonBlowUpIncrementalLowerData

end PrimitiveCarrierGeometryAndCardinalityClusteredBlowUpSubtheorems

namespace PrimitiveGeometryAndBlowUpSubtheorems

/-- Upgrade primitive coordinate upper data plus ordinary named lower blow-up
data to the cardinality-clustered finite-counting package. -/
noncomputable def toPrimitiveGeometryAndCardinalityClusteredBlowUpSubtheorems
    {P : TheoremOne.ProblemFamily.{u}}
    (h : PrimitiveGeometryAndBlowUpSubtheorems P) :
    PrimitiveGeometryAndCardinalityClusteredBlowUpSubtheorems P where
  upper_geometry := h.upper_geometry
  lower_karlsson :=
    h.lower_karlsson.toCardinalityClusteredKarlssonBlowUpIncrementalLowerData

end PrimitiveGeometryAndBlowUpSubtheorems

namespace PrimitiveCarrierGeometryAndBlowUpSubtheorems

/-- Upgrade carrier-certified primitive coordinate upper data plus ordinary
named lower blow-up data to the cardinality-clustered finite-counting package. -/
noncomputable def toPrimitiveCarrierGeometryAndCardinalityClusteredBlowUpSubtheorems
    {P : TheoremOne.ProblemFamily.{u}}
    (h : PrimitiveCarrierGeometryAndBlowUpSubtheorems P) :
    PrimitiveCarrierGeometryAndCardinalityClusteredBlowUpSubtheorems P where
  upper_geometry := h.upper_geometry
  lower_karlsson :=
    h.lower_karlsson.toCardinalityClusteredKarlssonBlowUpIncrementalLowerData

end PrimitiveCarrierGeometryAndBlowUpSubtheorems

/-- Primitive coordinate and pair-counted lower obligations for a family with
a named maximum count function. -/
def MaxPrimitiveGeometryAndPairCountedClusteredBlowUpSubtheorems
    (P : TheoremOne.MaxProblemFamily.{u}) : Type u :=
  PrimitiveGeometryAndPairCountedClusteredBlowUpSubtheorems P.toProblemFamily

/-- Carrier-certified primitive coordinate and pair-counted lower obligations
for a family with a named maximum count function. -/
def MaxPrimitiveCarrierGeometryAndPairCountedClusteredBlowUpSubtheorems
    (P : TheoremOne.MaxProblemFamily.{u}) : Type u :=
  PrimitiveCarrierGeometryAndPairCountedClusteredBlowUpSubtheorems
    P.toProblemFamily

/-- Primitive coordinate and fiber-counted lower obligations for a family with
a named maximum count function. -/
def MaxPrimitiveGeometryAndFiberCountedClusteredBlowUpSubtheorems
    (P : TheoremOne.MaxProblemFamily.{u}) : Type u :=
  PrimitiveGeometryAndFiberCountedClusteredBlowUpSubtheorems P.toProblemFamily

/-- Carrier-certified primitive coordinate and fiber-counted lower obligations
for a family with a named maximum count function. -/
def MaxPrimitiveCarrierGeometryAndFiberCountedClusteredBlowUpSubtheorems
    (P : TheoremOne.MaxProblemFamily.{u}) : Type u :=
  PrimitiveCarrierGeometryAndFiberCountedClusteredBlowUpSubtheorems
    P.toProblemFamily

/-- Primitive coordinate and cardinality-only lower obligations for a family
with a named maximum count function. -/
def MaxPrimitiveGeometryAndCardinalityClusteredBlowUpSubtheorems
    (P : TheoremOne.MaxProblemFamily.{u}) : Type u :=
  PrimitiveGeometryAndCardinalityClusteredBlowUpSubtheorems P.toProblemFamily

/-- Carrier-certified primitive coordinate and cardinality-only lower
obligations for a family with a named maximum count function. -/
def MaxPrimitiveCarrierGeometryAndCardinalityClusteredBlowUpSubtheorems
    (P : TheoremOne.MaxProblemFamily.{u}) : Type u :=
  PrimitiveCarrierGeometryAndCardinalityClusteredBlowUpSubtheorems
    P.toProblemFamily

/-- Maximum-form Theorem 1 from primitive coordinate lollipop records and a
pair-counted clustered Karlsson blow-up lower construction. -/
theorem theorem_one_statement_proven_from_primitive_geometry_and_pair_counted_clustered_blowup
    (P : TheoremOne.ProblemFamily.{u})
    (h : PrimitiveGeometryAndPairCountedClusteredBlowUpSubtheorems P) :
    TheoremOneFinal.TheoremOneStatement P := by
  exact theorem_one_statement_proven_from_primitive_geometry_and_clustered_blowup
    P h.toPrimitiveGeometryAndClusteredBlowUpSubtheorems

/-- Maximum-form Theorem 1 from carrier-certified primitive coordinate
lollipop records and a pair-counted clustered Karlsson blow-up lower
construction. -/
theorem theorem_one_statement_proven_from_primitive_carrier_geometry_and_pair_counted_clustered_blowup
    (P : TheoremOne.ProblemFamily.{u})
    (h : PrimitiveCarrierGeometryAndPairCountedClusteredBlowUpSubtheorems P) :
    TheoremOneFinal.TheoremOneStatement P := by
  exact theorem_one_statement_proven_from_primitive_carrier_geometry_and_clustered_blowup
    P h.toPrimitiveCarrierGeometryAndClusteredBlowUpSubtheorems

/-- Formula-form Theorem 1 from primitive coordinate lollipop records and a
pair-counted clustered Karlsson blow-up lower construction. -/
theorem theorem_one_formula_statement_proven_from_primitive_geometry_and_pair_counted_clustered_blowup
    (P : TheoremOne.MaxProblemFamily.{u})
    (h : MaxPrimitiveGeometryAndPairCountedClusteredBlowUpSubtheorems P) :
    TheoremOneFormulaStatement P := by
  exact theorem_one_formula_statement_proven_from_primitive_geometry_and_clustered_blowup
    P h.toPrimitiveGeometryAndClusteredBlowUpSubtheorems

/-- Formula-form Theorem 1 from carrier-certified primitive coordinate
lollipop records and a pair-counted clustered Karlsson blow-up lower
construction. -/
theorem theorem_one_formula_statement_proven_from_primitive_carrier_geometry_and_pair_counted_clustered_blowup
    (P : TheoremOne.MaxProblemFamily.{u})
    (h : MaxPrimitiveCarrierGeometryAndPairCountedClusteredBlowUpSubtheorems P) :
    TheoremOneFormulaStatement P := by
  exact theorem_one_formula_statement_proven_from_primitive_carrier_geometry_and_clustered_blowup
    P h.toPrimitiveCarrierGeometryAndClusteredBlowUpSubtheorems

/-- Single-size displayed formula from primitive coordinate lollipop records
and a pair-counted clustered Karlsson blow-up lower construction. -/
theorem theorem_one_formula_at_proven_from_primitive_geometry_and_pair_counted_clustered_blowup
    (P : TheoremOne.MaxProblemFamily.{u})
    (h : MaxPrimitiveGeometryAndPairCountedClusteredBlowUpSubtheorems P)
    (n : Nat) :
    P.aLop n =
      4 * ((n.choose 2 : Nat) : Rat) + manuscriptS n + (n : Rat) + 1 := by
  exact theorem_one_formula_statement_proven_from_primitive_geometry_and_pair_counted_clustered_blowup
    P h n

/-- Single-size displayed formula from carrier-certified primitive coordinate
lollipop records and a pair-counted clustered Karlsson blow-up lower
construction. -/
theorem theorem_one_formula_at_proven_from_primitive_carrier_geometry_and_pair_counted_clustered_blowup
    (P : TheoremOne.MaxProblemFamily.{u})
    (h : MaxPrimitiveCarrierGeometryAndPairCountedClusteredBlowUpSubtheorems P)
    (n : Nat) :
    P.aLop n =
      4 * ((n.choose 2 : Nat) : Rat) + manuscriptS n + (n : Rat) + 1 := by
  exact theorem_one_formula_statement_proven_from_primitive_carrier_geometry_and_pair_counted_clustered_blowup
    P h n

/-- Maximum-form Theorem 1 from primitive coordinate lollipop records and a
fiber-counted clustered Karlsson blow-up lower construction. -/
theorem theorem_one_statement_proven_from_primitive_geometry_and_fiber_counted_clustered_blowup
    (P : TheoremOne.ProblemFamily.{u})
    (h : PrimitiveGeometryAndFiberCountedClusteredBlowUpSubtheorems P) :
    TheoremOneFinal.TheoremOneStatement P := by
  exact theorem_one_statement_proven_from_primitive_geometry_and_pair_counted_clustered_blowup
    P h.toPrimitiveGeometryAndPairCountedClusteredBlowUpSubtheorems

/-- Maximum-form Theorem 1 from carrier-certified primitive coordinate
lollipop records and a fiber-counted clustered Karlsson blow-up lower
construction. -/
theorem theorem_one_statement_proven_from_primitive_carrier_geometry_and_fiber_counted_clustered_blowup
    (P : TheoremOne.ProblemFamily.{u})
    (h : PrimitiveCarrierGeometryAndFiberCountedClusteredBlowUpSubtheorems P) :
    TheoremOneFinal.TheoremOneStatement P := by
  exact theorem_one_statement_proven_from_primitive_carrier_geometry_and_pair_counted_clustered_blowup
    P h.toPrimitiveCarrierGeometryAndPairCountedClusteredBlowUpSubtheorems

/-- Formula-form Theorem 1 from primitive coordinate lollipop records and a
fiber-counted clustered Karlsson blow-up lower construction. -/
theorem theorem_one_formula_statement_proven_from_primitive_geometry_and_fiber_counted_clustered_blowup
    (P : TheoremOne.MaxProblemFamily.{u})
    (h : MaxPrimitiveGeometryAndFiberCountedClusteredBlowUpSubtheorems P) :
    TheoremOneFormulaStatement P := by
  exact theorem_one_formula_statement_proven_from_primitive_geometry_and_pair_counted_clustered_blowup
    P h.toPrimitiveGeometryAndPairCountedClusteredBlowUpSubtheorems

/-- Formula-form Theorem 1 from carrier-certified primitive coordinate
lollipop records and a fiber-counted clustered Karlsson blow-up lower
construction. -/
theorem theorem_one_formula_statement_proven_from_primitive_carrier_geometry_and_fiber_counted_clustered_blowup
    (P : TheoremOne.MaxProblemFamily.{u})
    (h : MaxPrimitiveCarrierGeometryAndFiberCountedClusteredBlowUpSubtheorems P) :
    TheoremOneFormulaStatement P := by
  exact theorem_one_formula_statement_proven_from_primitive_carrier_geometry_and_pair_counted_clustered_blowup
    P h.toPrimitiveCarrierGeometryAndPairCountedClusteredBlowUpSubtheorems

/-- Single-size displayed formula from primitive coordinate lollipop records
and a fiber-counted clustered Karlsson blow-up lower construction. -/
theorem theorem_one_formula_at_proven_from_primitive_geometry_and_fiber_counted_clustered_blowup
    (P : TheoremOne.MaxProblemFamily.{u})
    (h : MaxPrimitiveGeometryAndFiberCountedClusteredBlowUpSubtheorems P)
    (n : Nat) :
    P.aLop n =
      4 * ((n.choose 2 : Nat) : Rat) + manuscriptS n + (n : Rat) + 1 := by
  exact theorem_one_formula_statement_proven_from_primitive_geometry_and_fiber_counted_clustered_blowup
    P h n

/-- Single-size displayed formula from carrier-certified primitive coordinate
lollipop records and a fiber-counted clustered Karlsson blow-up lower
construction. -/
theorem theorem_one_formula_at_proven_from_primitive_carrier_geometry_and_fiber_counted_clustered_blowup
    (P : TheoremOne.MaxProblemFamily.{u})
    (h : MaxPrimitiveCarrierGeometryAndFiberCountedClusteredBlowUpSubtheorems P)
    (n : Nat) :
    P.aLop n =
      4 * ((n.choose 2 : Nat) : Rat) + manuscriptS n + (n : Rat) + 1 := by
  exact theorem_one_formula_statement_proven_from_primitive_carrier_geometry_and_fiber_counted_clustered_blowup
    P h n

/-- Maximum-form Theorem 1 from primitive coordinate lollipop records and a
cardinality-only clustered Karlsson blow-up lower construction. -/
theorem theorem_one_statement_proven_from_primitive_geometry_and_cardinality_clustered_blowup
    (P : TheoremOne.ProblemFamily.{u})
    (h : PrimitiveGeometryAndCardinalityClusteredBlowUpSubtheorems P) :
    TheoremOneFinal.TheoremOneStatement P := by
  exact theorem_one_statement_proven_from_primitive_geometry_and_fiber_counted_clustered_blowup
    P h.toPrimitiveGeometryAndFiberCountedClusteredBlowUpSubtheorems

/-- Maximum-form Theorem 1 from carrier-certified primitive coordinate
lollipop records and a cardinality-only clustered Karlsson blow-up lower
construction. -/
theorem theorem_one_statement_proven_from_primitive_carrier_geometry_and_cardinality_clustered_blowup
    (P : TheoremOne.ProblemFamily.{u})
    (h : PrimitiveCarrierGeometryAndCardinalityClusteredBlowUpSubtheorems P) :
    TheoremOneFinal.TheoremOneStatement P := by
  exact theorem_one_statement_proven_from_primitive_carrier_geometry_and_fiber_counted_clustered_blowup
    P h.toPrimitiveCarrierGeometryAndFiberCountedClusteredBlowUpSubtheorems

/-- Formula-form Theorem 1 from primitive coordinate lollipop records and a
cardinality-only clustered Karlsson blow-up lower construction. -/
theorem theorem_one_formula_statement_proven_from_primitive_geometry_and_cardinality_clustered_blowup
    (P : TheoremOne.MaxProblemFamily.{u})
    (h : MaxPrimitiveGeometryAndCardinalityClusteredBlowUpSubtheorems P) :
    TheoremOneFormulaStatement P := by
  exact theorem_one_formula_statement_proven_from_primitive_geometry_and_fiber_counted_clustered_blowup
    P h.toPrimitiveGeometryAndFiberCountedClusteredBlowUpSubtheorems

/-- Formula-form Theorem 1 from carrier-certified primitive coordinate
lollipop records and a cardinality-only clustered Karlsson blow-up lower
construction. -/
theorem theorem_one_formula_statement_proven_from_primitive_carrier_geometry_and_cardinality_clustered_blowup
    (P : TheoremOne.MaxProblemFamily.{u})
    (h : MaxPrimitiveCarrierGeometryAndCardinalityClusteredBlowUpSubtheorems P) :
    TheoremOneFormulaStatement P := by
  exact theorem_one_formula_statement_proven_from_primitive_carrier_geometry_and_fiber_counted_clustered_blowup
    P h.toPrimitiveCarrierGeometryAndFiberCountedClusteredBlowUpSubtheorems

/-- Single-size displayed formula from primitive coordinate lollipop records
and a cardinality-only clustered Karlsson blow-up lower construction. -/
theorem theorem_one_formula_at_proven_from_primitive_geometry_and_cardinality_clustered_blowup
    (P : TheoremOne.MaxProblemFamily.{u})
    (h : MaxPrimitiveGeometryAndCardinalityClusteredBlowUpSubtheorems P)
    (n : Nat) :
    P.aLop n =
      4 * ((n.choose 2 : Nat) : Rat) + manuscriptS n + (n : Rat) + 1 := by
  exact theorem_one_formula_statement_proven_from_primitive_geometry_and_cardinality_clustered_blowup
    P h n

/-- Single-size displayed formula from carrier-certified primitive coordinate
lollipop records and a cardinality-only clustered Karlsson blow-up lower
construction. -/
theorem theorem_one_formula_at_proven_from_primitive_carrier_geometry_and_cardinality_clustered_blowup
    (P : TheoremOne.MaxProblemFamily.{u})
    (h : MaxPrimitiveCarrierGeometryAndCardinalityClusteredBlowUpSubtheorems P)
    (n : Nat) :
    P.aLop n =
      4 * ((n.choose 2 : Nat) : Rat) + manuscriptS n + (n : Rat) + 1 := by
  exact theorem_one_formula_statement_proven_from_primitive_carrier_geometry_and_cardinality_clustered_blowup
    P h n

end PrimitiveGeometry
end TheoremOneManuscript
end Lollipop
