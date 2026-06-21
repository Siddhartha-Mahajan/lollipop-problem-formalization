import Lollipop.Internal.Manuscript.ExplicitInputs.EndToEnd
import Lollipop.Internal.Manuscript.PrimitiveGeometry.Basic

/-!
Theorem 1 endpoints from primitive coordinate lollipop records.

The upper side here names actual lollipop point sets, but still takes the
hard Euclidean crossing-count table and incremental region data as
certificates.  The lower side uses the named Karlsson blow-up construction
data from `ExplicitInputs`.
-/

namespace Lollipop
namespace TheoremOneManuscript
namespace PrimitiveGeometry

universe u

/-- Primitive coordinate upper data plus a named Karlsson blow-up lower
construction. -/
structure PrimitiveGeometryAndBlowUpSubtheorems
    (P : TheoremOne.ProblemFamily.{u}) where
  upper_geometry : PrimitiveExactUpperGeometryData P
  lower_karlsson : ExplicitInputs.KarlssonBlowUpIncrementalLowerData P

namespace PrimitiveGeometryAndBlowUpSubtheorems

/-- Convert primitive coordinate lollipop records into the explicit concrete
blow-up package used by the proved theorem stack. -/
def toConcreteFullyIncrementalBlowUpModelSubtheorems
    {P : TheoremOne.ProblemFamily.{u}}
    (h : PrimitiveGeometryAndBlowUpSubtheorems P) :
    ExplicitInputs.ConcreteFullyIncrementalBlowUpModelSubtheorems P where
  upper_geometry := h.upper_geometry.toCanonicalExactUpperGeometryIncrementalData
  lower_karlsson := h.lower_karlsson

end PrimitiveGeometryAndBlowUpSubtheorems

/-- Carrier-certified primitive coordinate upper data plus a named Karlsson
blow-up lower construction. -/
structure PrimitiveCarrierGeometryAndBlowUpSubtheorems
    (P : TheoremOne.ProblemFamily.{u}) where
  upper_geometry : PrimitiveCarrierCertifiedExactUpperGeometryData P
  lower_karlsson : ExplicitInputs.KarlssonBlowUpIncrementalLowerData P

namespace PrimitiveCarrierGeometryAndBlowUpSubtheorems

/-- Forget the finite carrier-intersection witnesses after converting them to
the primitive exact upper package. -/
def toPrimitiveGeometryAndBlowUpSubtheorems
    {P : TheoremOne.ProblemFamily.{u}}
    (h : PrimitiveCarrierGeometryAndBlowUpSubtheorems P) :
    PrimitiveGeometryAndBlowUpSubtheorems P where
  upper_geometry := h.upper_geometry.toPrimitiveExactUpperGeometryData
  lower_karlsson := h.lower_karlsson

end PrimitiveCarrierGeometryAndBlowUpSubtheorems

/-- Primitive coordinate upper data plus a four-cluster-table-certified
Karlsson blow-up lower construction. -/
structure PrimitiveGeometryAndTableBlowUpSubtheorems
    (P : TheoremOne.ProblemFamily.{u}) where
  upper_geometry : PrimitiveExactUpperGeometryData P
  lower_karlsson : ExplicitInputs.KarlssonTableBlowUpIncrementalLowerData P

namespace PrimitiveGeometryAndTableBlowUpSubtheorems

/-- Convert table-certified lower data to the named-blow-up primitive package
after Lean derives the lower crossing polynomial from the table sum. -/
def toPrimitiveGeometryAndBlowUpSubtheorems
    {P : TheoremOne.ProblemFamily.{u}}
    (h : PrimitiveGeometryAndTableBlowUpSubtheorems P) :
    PrimitiveGeometryAndBlowUpSubtheorems P where
  upper_geometry := h.upper_geometry
  lower_karlsson := h.lower_karlsson.toKarlssonBlowUpIncrementalLowerData

end PrimitiveGeometryAndTableBlowUpSubtheorems

/-- Carrier-certified primitive coordinate upper data plus a
four-cluster-table-certified Karlsson blow-up lower construction. -/
structure PrimitiveCarrierGeometryAndTableBlowUpSubtheorems
    (P : TheoremOne.ProblemFamily.{u}) where
  upper_geometry : PrimitiveCarrierCertifiedExactUpperGeometryData P
  lower_karlsson : ExplicitInputs.KarlssonTableBlowUpIncrementalLowerData P

namespace PrimitiveCarrierGeometryAndTableBlowUpSubtheorems

/-- Forget carrier-intersection witnesses and convert table-certified lower
data to the named-blow-up primitive package. -/
def toPrimitiveCarrierGeometryAndBlowUpSubtheorems
    {P : TheoremOne.ProblemFamily.{u}}
    (h : PrimitiveCarrierGeometryAndTableBlowUpSubtheorems P) :
    PrimitiveCarrierGeometryAndBlowUpSubtheorems P where
  upper_geometry := h.upper_geometry
  lower_karlsson := h.lower_karlsson.toKarlssonBlowUpIncrementalLowerData

end PrimitiveCarrierGeometryAndTableBlowUpSubtheorems

/-- Primitive coordinate upper data plus a clustered Karlsson blow-up lower
construction. -/
structure PrimitiveGeometryAndClusteredBlowUpSubtheorems
    (P : TheoremOne.ProblemFamily.{u}) where
  upper_geometry : PrimitiveExactUpperGeometryData P
  lower_karlsson : ExplicitInputs.ClusteredKarlssonBlowUpIncrementalLowerData P

namespace PrimitiveGeometryAndClusteredBlowUpSubtheorems

/-- Convert clustered lower data to the table-certified primitive package. -/
def toPrimitiveGeometryAndTableBlowUpSubtheorems
    {P : TheoremOne.ProblemFamily.{u}}
    (h : PrimitiveGeometryAndClusteredBlowUpSubtheorems P) :
    PrimitiveGeometryAndTableBlowUpSubtheorems P where
  upper_geometry := h.upper_geometry
  lower_karlsson := h.lower_karlsson.toKarlssonTableBlowUpIncrementalLowerData

end PrimitiveGeometryAndClusteredBlowUpSubtheorems

/-- Carrier-certified primitive coordinate upper data plus a clustered
Karlsson blow-up lower construction. -/
structure PrimitiveCarrierGeometryAndClusteredBlowUpSubtheorems
    (P : TheoremOne.ProblemFamily.{u}) where
  upper_geometry : PrimitiveCarrierCertifiedExactUpperGeometryData P
  lower_karlsson : ExplicitInputs.ClusteredKarlssonBlowUpIncrementalLowerData P

namespace PrimitiveCarrierGeometryAndClusteredBlowUpSubtheorems

/-- Convert clustered lower data to the table-certified primitive carrier
package. -/
def toPrimitiveCarrierGeometryAndTableBlowUpSubtheorems
    {P : TheoremOne.ProblemFamily.{u}}
    (h : PrimitiveCarrierGeometryAndClusteredBlowUpSubtheorems P) :
    PrimitiveCarrierGeometryAndTableBlowUpSubtheorems P where
  upper_geometry := h.upper_geometry
  lower_karlsson := h.lower_karlsson.toKarlssonTableBlowUpIncrementalLowerData

end PrimitiveCarrierGeometryAndClusteredBlowUpSubtheorems

/-- Maximum-form Theorem 1 from primitive coordinate lollipop records and a
named Karlsson blow-up lower construction. -/
theorem theorem_one_statement_proven_from_primitive_geometry_and_blowup
    (P : TheoremOne.ProblemFamily.{u})
    (h : PrimitiveGeometryAndBlowUpSubtheorems P) :
    TheoremOneFinal.TheoremOneStatement P := by
  exact
    ExplicitInputs.theorem_one_statement_proven_from_concrete_blowup_model
      P h.toConcreteFullyIncrementalBlowUpModelSubtheorems

/-- Maximum-form Theorem 1 from carrier-certified primitive coordinate
lollipop records and a named Karlsson blow-up lower construction. -/
theorem theorem_one_statement_proven_from_primitive_carrier_geometry_and_blowup
    (P : TheoremOne.ProblemFamily.{u})
    (h : PrimitiveCarrierGeometryAndBlowUpSubtheorems P) :
    TheoremOneFinal.TheoremOneStatement P := by
  exact theorem_one_statement_proven_from_primitive_geometry_and_blowup
    P h.toPrimitiveGeometryAndBlowUpSubtheorems

/-- Maximum-form Theorem 1 from primitive coordinate lollipop records and a
four-cluster-table-certified Karlsson blow-up lower construction. -/
theorem theorem_one_statement_proven_from_primitive_geometry_and_table_blowup
    (P : TheoremOne.ProblemFamily.{u})
    (h : PrimitiveGeometryAndTableBlowUpSubtheorems P) :
    TheoremOneFinal.TheoremOneStatement P := by
  exact theorem_one_statement_proven_from_primitive_geometry_and_blowup
    P h.toPrimitiveGeometryAndBlowUpSubtheorems

/-- Maximum-form Theorem 1 from carrier-certified primitive coordinate
lollipop records and a four-cluster-table-certified Karlsson blow-up lower
construction. -/
theorem theorem_one_statement_proven_from_primitive_carrier_geometry_and_table_blowup
    (P : TheoremOne.ProblemFamily.{u})
    (h : PrimitiveCarrierGeometryAndTableBlowUpSubtheorems P) :
    TheoremOneFinal.TheoremOneStatement P := by
  exact theorem_one_statement_proven_from_primitive_carrier_geometry_and_blowup
    P h.toPrimitiveCarrierGeometryAndBlowUpSubtheorems

/-- Maximum-form Theorem 1 from primitive coordinate lollipop records and a
clustered Karlsson blow-up lower construction. -/
theorem theorem_one_statement_proven_from_primitive_geometry_and_clustered_blowup
    (P : TheoremOne.ProblemFamily.{u})
    (h : PrimitiveGeometryAndClusteredBlowUpSubtheorems P) :
    TheoremOneFinal.TheoremOneStatement P := by
  exact theorem_one_statement_proven_from_primitive_geometry_and_table_blowup
    P h.toPrimitiveGeometryAndTableBlowUpSubtheorems

/-- Maximum-form Theorem 1 from carrier-certified primitive coordinate
lollipop records and a clustered Karlsson blow-up lower construction. -/
theorem theorem_one_statement_proven_from_primitive_carrier_geometry_and_clustered_blowup
    (P : TheoremOne.ProblemFamily.{u})
    (h : PrimitiveCarrierGeometryAndClusteredBlowUpSubtheorems P) :
    TheoremOneFinal.TheoremOneStatement P := by
  exact theorem_one_statement_proven_from_primitive_carrier_geometry_and_table_blowup
    P h.toPrimitiveCarrierGeometryAndTableBlowUpSubtheorems

/-- Primitive coordinate lollipop and named-blow-up obligations for a family
with a named maximum count function. -/
def MaxPrimitiveGeometryAndBlowUpSubtheorems
    (P : TheoremOne.MaxProblemFamily.{u}) : Type u :=
  PrimitiveGeometryAndBlowUpSubtheorems P.toProblemFamily

/-- Carrier-certified primitive coordinate lollipop and named-blow-up
obligations for a family with a named maximum count function. -/
def MaxPrimitiveCarrierGeometryAndBlowUpSubtheorems
    (P : TheoremOne.MaxProblemFamily.{u}) : Type u :=
  PrimitiveCarrierGeometryAndBlowUpSubtheorems P.toProblemFamily

/-- Primitive coordinate lollipop and table-certified named-blow-up
obligations for a family with a named maximum count function. -/
def MaxPrimitiveGeometryAndTableBlowUpSubtheorems
    (P : TheoremOne.MaxProblemFamily.{u}) : Type u :=
  PrimitiveGeometryAndTableBlowUpSubtheorems P.toProblemFamily

/-- Carrier-certified primitive coordinate lollipop and table-certified
named-blow-up obligations for a family with a named maximum count function. -/
def MaxPrimitiveCarrierGeometryAndTableBlowUpSubtheorems
    (P : TheoremOne.MaxProblemFamily.{u}) : Type u :=
  PrimitiveCarrierGeometryAndTableBlowUpSubtheorems P.toProblemFamily

/-- Primitive coordinate lollipop and clustered named-blow-up obligations for
a family with a named maximum count function. -/
def MaxPrimitiveGeometryAndClusteredBlowUpSubtheorems
    (P : TheoremOne.MaxProblemFamily.{u}) : Type u :=
  PrimitiveGeometryAndClusteredBlowUpSubtheorems P.toProblemFamily

/-- Carrier-certified primitive coordinate lollipop and clustered named-blow-up
obligations for a family with a named maximum count function. -/
def MaxPrimitiveCarrierGeometryAndClusteredBlowUpSubtheorems
    (P : TheoremOne.MaxProblemFamily.{u}) : Type u :=
  PrimitiveCarrierGeometryAndClusteredBlowUpSubtheorems P.toProblemFamily

/-- Formula-form Theorem 1 from primitive coordinate lollipop records and a
named Karlsson blow-up lower construction. -/
theorem theorem_one_formula_statement_proven_from_primitive_geometry_and_blowup
    (P : TheoremOne.MaxProblemFamily.{u})
    (h : MaxPrimitiveGeometryAndBlowUpSubtheorems P) :
    TheoremOneFormulaStatement P := by
  exact
    ExplicitInputs.theorem_one_formula_statement_proven_from_concrete_blowup_model
      P h.toConcreteFullyIncrementalBlowUpModelSubtheorems

/-- Formula-form Theorem 1 from carrier-certified primitive coordinate
lollipop records and a named Karlsson blow-up lower construction. -/
theorem theorem_one_formula_statement_proven_from_primitive_carrier_geometry_and_blowup
    (P : TheoremOne.MaxProblemFamily.{u})
    (h : MaxPrimitiveCarrierGeometryAndBlowUpSubtheorems P) :
    TheoremOneFormulaStatement P := by
  exact theorem_one_formula_statement_proven_from_primitive_geometry_and_blowup
    P h.toPrimitiveGeometryAndBlowUpSubtheorems

/-- Formula-form Theorem 1 from primitive coordinate lollipop records and a
four-cluster-table-certified Karlsson blow-up lower construction. -/
theorem theorem_one_formula_statement_proven_from_primitive_geometry_and_table_blowup
    (P : TheoremOne.MaxProblemFamily.{u})
    (h : MaxPrimitiveGeometryAndTableBlowUpSubtheorems P) :
    TheoremOneFormulaStatement P := by
  exact theorem_one_formula_statement_proven_from_primitive_geometry_and_blowup
    P h.toPrimitiveGeometryAndBlowUpSubtheorems

/-- Formula-form Theorem 1 from carrier-certified primitive coordinate
lollipop records and a four-cluster-table-certified Karlsson blow-up lower
construction. -/
theorem theorem_one_formula_statement_proven_from_primitive_carrier_geometry_and_table_blowup
    (P : TheoremOne.MaxProblemFamily.{u})
    (h : MaxPrimitiveCarrierGeometryAndTableBlowUpSubtheorems P) :
    TheoremOneFormulaStatement P := by
  exact theorem_one_formula_statement_proven_from_primitive_carrier_geometry_and_blowup
    P h.toPrimitiveCarrierGeometryAndBlowUpSubtheorems

/-- Formula-form Theorem 1 from primitive coordinate lollipop records and a
clustered Karlsson blow-up lower construction. -/
theorem theorem_one_formula_statement_proven_from_primitive_geometry_and_clustered_blowup
    (P : TheoremOne.MaxProblemFamily.{u})
    (h : MaxPrimitiveGeometryAndClusteredBlowUpSubtheorems P) :
    TheoremOneFormulaStatement P := by
  exact theorem_one_formula_statement_proven_from_primitive_geometry_and_table_blowup
    P h.toPrimitiveGeometryAndTableBlowUpSubtheorems

/-- Formula-form Theorem 1 from carrier-certified primitive coordinate
lollipop records and a clustered Karlsson blow-up lower construction. -/
theorem theorem_one_formula_statement_proven_from_primitive_carrier_geometry_and_clustered_blowup
    (P : TheoremOne.MaxProblemFamily.{u})
    (h : MaxPrimitiveCarrierGeometryAndClusteredBlowUpSubtheorems P) :
    TheoremOneFormulaStatement P := by
  exact theorem_one_formula_statement_proven_from_primitive_carrier_geometry_and_table_blowup
    P h.toPrimitiveCarrierGeometryAndTableBlowUpSubtheorems

/-- Single-size displayed formula from primitive coordinate lollipop records
and a named Karlsson blow-up lower construction. -/
theorem theorem_one_formula_at_proven_from_primitive_geometry_and_blowup
    (P : TheoremOne.MaxProblemFamily.{u})
    (h : MaxPrimitiveGeometryAndBlowUpSubtheorems P)
    (n : Nat) :
    P.aLop n =
      4 * ((n.choose 2 : Nat) : Rat) + manuscriptS n + (n : Rat) + 1 := by
  exact theorem_one_formula_statement_proven_from_primitive_geometry_and_blowup P h n

/-- Single-size displayed formula from carrier-certified primitive coordinate
lollipop records and a named Karlsson blow-up lower construction. -/
theorem theorem_one_formula_at_proven_from_primitive_carrier_geometry_and_blowup
    (P : TheoremOne.MaxProblemFamily.{u})
    (h : MaxPrimitiveCarrierGeometryAndBlowUpSubtheorems P)
    (n : Nat) :
    P.aLop n =
      4 * ((n.choose 2 : Nat) : Rat) + manuscriptS n + (n : Rat) + 1 := by
  exact theorem_one_formula_statement_proven_from_primitive_carrier_geometry_and_blowup P h n

/-- Single-size displayed formula from primitive coordinate lollipop records
and a four-cluster-table-certified Karlsson blow-up lower construction. -/
theorem theorem_one_formula_at_proven_from_primitive_geometry_and_table_blowup
    (P : TheoremOne.MaxProblemFamily.{u})
    (h : MaxPrimitiveGeometryAndTableBlowUpSubtheorems P)
    (n : Nat) :
    P.aLop n =
      4 * ((n.choose 2 : Nat) : Rat) + manuscriptS n + (n : Rat) + 1 := by
  exact theorem_one_formula_statement_proven_from_primitive_geometry_and_table_blowup P h n

/-- Single-size displayed formula from carrier-certified primitive coordinate
lollipop records and a four-cluster-table-certified Karlsson blow-up lower
construction. -/
theorem theorem_one_formula_at_proven_from_primitive_carrier_geometry_and_table_blowup
    (P : TheoremOne.MaxProblemFamily.{u})
    (h : MaxPrimitiveCarrierGeometryAndTableBlowUpSubtheorems P)
    (n : Nat) :
    P.aLop n =
      4 * ((n.choose 2 : Nat) : Rat) + manuscriptS n + (n : Rat) + 1 := by
  exact theorem_one_formula_statement_proven_from_primitive_carrier_geometry_and_table_blowup P h n

/-- Single-size displayed formula from primitive coordinate lollipop records
and a clustered Karlsson blow-up lower construction. -/
theorem theorem_one_formula_at_proven_from_primitive_geometry_and_clustered_blowup
    (P : TheoremOne.MaxProblemFamily.{u})
    (h : MaxPrimitiveGeometryAndClusteredBlowUpSubtheorems P)
    (n : Nat) :
    P.aLop n =
      4 * ((n.choose 2 : Nat) : Rat) + manuscriptS n + (n : Rat) + 1 := by
  exact theorem_one_formula_statement_proven_from_primitive_geometry_and_clustered_blowup P h n

/-- Single-size displayed formula from carrier-certified primitive coordinate
lollipop records and a clustered Karlsson blow-up lower construction. -/
theorem theorem_one_formula_at_proven_from_primitive_carrier_geometry_and_clustered_blowup
    (P : TheoremOne.MaxProblemFamily.{u})
    (h : MaxPrimitiveCarrierGeometryAndClusteredBlowUpSubtheorems P)
    (n : Nat) :
    P.aLop n =
      4 * ((n.choose 2 : Nat) : Rat) + manuscriptS n + (n : Rat) + 1 := by
  exact theorem_one_formula_statement_proven_from_primitive_carrier_geometry_and_clustered_blowup P h n

end PrimitiveGeometry
end TheoremOneManuscript
end Lollipop
