import Lollipop.Internal.Manuscript.PrimitiveGeometry.PairCountedEndToEnd
import Lollipop.Internal.Manuscript.Proof

/-!
Minimal theorem bridge for the final manuscript formalization.

The lower-bound stack used by the final theorem routes through the
cardinality-clustered Karlsson blow-up construction.  This file exposes only
that bridge, avoiding the older collection of theorem-one wrapper variants.
-/

namespace Lollipop
namespace TheoremOneManuscript

universe u

/-- Manuscript Theorem 1 in displayed formula form from concrete upper data
and a cardinality-only clustered Karlsson blow-up lower construction. -/
theorem theorem_one_from_cardinality_clustered_blowup
    (P : TheoremOne.MaxProblemFamily.{u})
    (h :
      ExplicitInputs.MaxConcreteFullyIncrementalCardinalityClusteredBlowUpModelSubtheorems
        P) :
    TheoremOneFormulaStatement P := by
  exact
    ExplicitInputs.theorem_one_formula_statement_proven_from_concrete_cardinality_clustered_blowup_model
      P h

/-- Manuscript Theorem 1 in displayed formula form from paper-style geometric
upper data and a cardinality-only clustered Karlsson blow-up lower
construction. -/
theorem theorem_one_from_geometric_data_and_cardinality_clustered_blowup
    (P : TheoremOne.MaxProblemFamily.{u})
    (h :
      ExplicitInputs.MaxManuscriptGeometricCardinalityClusteredBlowUpDataSubtheorems
        P) :
    TheoremOneFormulaStatement P := by
  exact
    ExplicitInputs.theorem_one_formula_statement_proven_from_geometric_data_and_cardinality_clustered_blowup
      P h

/-- Manuscript Theorem 1 in displayed formula form from primitive coordinate
lollipop records and a cardinality-only clustered Karlsson blow-up lower
construction. -/
theorem theorem_one_from_primitive_geometry_and_cardinality_clustered_blowup
    (P : TheoremOne.MaxProblemFamily.{u})
    (h : PrimitiveGeometry.MaxPrimitiveGeometryAndCardinalityClusteredBlowUpSubtheorems
      P) :
    TheoremOneFormulaStatement P := by
  exact
    PrimitiveGeometry.theorem_one_formula_statement_proven_from_primitive_geometry_and_cardinality_clustered_blowup
      P h

/-- Manuscript Theorem 1 in displayed formula form from carrier-certified
primitive coordinate lollipop records and a cardinality-only clustered
Karlsson blow-up lower construction. -/
theorem theorem_one_from_primitive_carrier_geometry_and_cardinality_clustered_blowup
    (P : TheoremOne.MaxProblemFamily.{u})
    (h :
      PrimitiveGeometry.MaxPrimitiveCarrierGeometryAndCardinalityClusteredBlowUpSubtheorems
        P) :
    TheoremOneFormulaStatement P := by
  exact
    PrimitiveGeometry.theorem_one_formula_statement_proven_from_primitive_carrier_geometry_and_cardinality_clustered_blowup
      P h

end TheoremOneManuscript
end Lollipop
