import Lollipop.Internal.Manuscript.ConcreteModel
import Lollipop.Internal.Manuscript.ExplicitInputs.EndToEnd
import Lollipop.Internal.Manuscript.GeometricInputs
import Lollipop.Internal.Manuscript.PrimitiveGeometry.EndToEnd

/-!
Final manuscript-facing Theorem 1 entry points.

The files in this folder expose the paper's displayed formula using the sorted
finite extremum `manuscriptS`.  This file gives short theorem names for the
strongest current concrete endpoint: exact canonical upper geometry with the
upper region equation proved from the previous-pair insertion recurrence, and
sorted Karlsson lower data with the lower region equation proved from
incremental insertion data.
-/

namespace Lollipop
namespace TheoremOneManuscript

universe u

/-- Manuscript Theorem 1 in maximum form, from fully incremental concrete
upper/lower model subtheorems. -/
theorem theorem_one_maximum
    (P : TheoremOne.ProblemFamily.{u})
    (h : ConcreteFullyIncrementalModelSubtheorems P) :
    TheoremOneFinal.TheoremOneStatement P := by
  exact theorem_one_statement_proven_from_fully_incremental_concrete_model P h

/-- Manuscript Theorem 1 in the displayed formula form, using the sorted
definition of `S(n)`. -/
theorem theorem_one
    (P : TheoremOne.MaxProblemFamily.{u})
    (h : MaxConcreteFullyIncrementalModelSubtheorems P) :
    TheoremOneFormulaStatement P := by
  exact theorem_one_formula_statement_proven_from_fully_incremental_concrete_model P h

/-- Single-size form of the manuscript's displayed Theorem 1 formula. -/
theorem theorem_one_at
    (P : TheoremOne.MaxProblemFamily.{u})
    (h : MaxConcreteFullyIncrementalModelSubtheorems P)
    (n : Nat) :
    P.aLop n =
      4 * ((n.choose 2 : Nat) : Rat) + manuscriptS n + (n : Rat) + 1 := by
  exact theorem_one P h n

/-- Manuscript Theorem 1 in maximum form from the paper-style
close/intriguing geometric input and incremental sorted Karlsson lower data. -/
theorem theorem_one_maximum_from_geometric_inputs
    (P : TheoremOne.ProblemFamily.{u})
    (h : ManuscriptGeometricIncrementalModelSubtheorems P) :
    TheoremOneFinal.TheoremOneStatement P := by
  exact theorem_one_statement_proven_from_manuscript_geometric_incremental_model P h

/-- Manuscript Theorem 1 in displayed formula form from the paper-style
close/intriguing geometric input and incremental sorted Karlsson lower data. -/
theorem theorem_one_from_geometric_inputs
    (P : TheoremOne.MaxProblemFamily.{u})
    (h : MaxManuscriptGeometricIncrementalModelSubtheorems P) :
    TheoremOneFormulaStatement P := by
  exact theorem_one_formula_statement_proven_from_manuscript_geometric_incremental_model P h

/-- Single-size displayed formula from the paper-style close/intriguing
geometric input and incremental sorted Karlsson lower data. -/
theorem theorem_one_at_from_geometric_inputs
    (P : TheoremOne.MaxProblemFamily.{u})
    (h : MaxManuscriptGeometricIncrementalModelSubtheorems P)
    (n : Nat) :
    P.aLop n =
      4 * ((n.choose 2 : Nat) : Rat) + manuscriptS n + (n : Rat) + 1 := by
  exact theorem_one_from_geometric_inputs P h n

/-- Manuscript Theorem 1 in maximum form from fully incremental global
paper-style geometric extractor data. -/
theorem theorem_one_maximum_from_geometric_data
    (P : TheoremOne.ProblemFamily.{u})
    (h : ManuscriptGeometricFullyIncrementalDataSubtheorems P) :
    TheoremOneFinal.TheoremOneStatement P := by
  exact theorem_one_statement_proven_from_manuscript_geometric_fully_incremental_data P h

/-- Manuscript Theorem 1 in displayed formula form from fully incremental
global paper-style geometric extractor data. -/
theorem theorem_one_from_geometric_data
    (P : TheoremOne.MaxProblemFamily.{u})
    (h : MaxManuscriptGeometricFullyIncrementalDataSubtheorems P) :
    TheoremOneFormulaStatement P := by
  exact theorem_one_formula_statement_proven_from_manuscript_geometric_fully_incremental_data P h

/-- Single-size displayed formula from fully incremental global paper-style
geometric extractor data. -/
theorem theorem_one_at_from_geometric_data
    (P : TheoremOne.MaxProblemFamily.{u})
    (h : MaxManuscriptGeometricFullyIncrementalDataSubtheorems P)
    (n : Nat) :
    P.aLop n =
      4 * ((n.choose 2 : Nat) : Rat) + manuscriptS n + (n : Rat) + 1 := by
  exact theorem_one_from_geometric_data P h n

/-- Manuscript Theorem 1 in maximum form from concrete upper data and a named
Karlsson blow-up lower construction. -/
theorem theorem_one_maximum_from_explicit_blowup
    (P : TheoremOne.ProblemFamily.{u})
    (h : ExplicitInputs.ConcreteFullyIncrementalBlowUpModelSubtheorems P) :
    TheoremOneFinal.TheoremOneStatement P := by
  exact ExplicitInputs.theorem_one_statement_proven_from_concrete_blowup_model P h

/-- Manuscript Theorem 1 in displayed formula form from concrete upper data
and a named Karlsson blow-up lower construction. -/
theorem theorem_one_from_explicit_blowup
    (P : TheoremOne.MaxProblemFamily.{u})
    (h : ExplicitInputs.MaxConcreteFullyIncrementalBlowUpModelSubtheorems P) :
    TheoremOneFormulaStatement P := by
  exact ExplicitInputs.theorem_one_formula_statement_proven_from_concrete_blowup_model P h

/-- Single-size displayed formula from concrete upper data and a named
Karlsson blow-up lower construction. -/
theorem theorem_one_at_from_explicit_blowup
    (P : TheoremOne.MaxProblemFamily.{u})
    (h : ExplicitInputs.MaxConcreteFullyIncrementalBlowUpModelSubtheorems P)
    (n : Nat) :
    P.aLop n =
      4 * ((n.choose 2 : Nat) : Rat) + manuscriptS n + (n : Rat) + 1 := by
  exact theorem_one_from_explicit_blowup P h n

/-- Manuscript Theorem 1 in maximum form from paper-style geometric upper
data and a named Karlsson blow-up lower construction. -/
theorem theorem_one_maximum_from_geometric_data_and_explicit_blowup
    (P : TheoremOne.ProblemFamily.{u})
    (h : ExplicitInputs.ManuscriptGeometricBlowUpDataSubtheorems P) :
    TheoremOneFinal.TheoremOneStatement P := by
  exact ExplicitInputs.theorem_one_statement_proven_from_geometric_data_and_blowup P h

/-- Manuscript Theorem 1 in displayed formula form from paper-style
geometric upper data and a named Karlsson blow-up lower construction. -/
theorem theorem_one_from_geometric_data_and_explicit_blowup
    (P : TheoremOne.MaxProblemFamily.{u})
    (h : ExplicitInputs.MaxManuscriptGeometricBlowUpDataSubtheorems P) :
    TheoremOneFormulaStatement P := by
  exact ExplicitInputs.theorem_one_formula_statement_proven_from_geometric_data_and_blowup P h

/-- Single-size displayed formula from paper-style geometric upper data and a
named Karlsson blow-up lower construction. -/
theorem theorem_one_at_from_geometric_data_and_explicit_blowup
    (P : TheoremOne.MaxProblemFamily.{u})
    (h : ExplicitInputs.MaxManuscriptGeometricBlowUpDataSubtheorems P)
    (n : Nat) :
    P.aLop n =
      4 * ((n.choose 2 : Nat) : Rat) + manuscriptS n + (n : Rat) + 1 := by
  exact theorem_one_from_geometric_data_and_explicit_blowup P h n

/-- Manuscript Theorem 1 in maximum form from concrete upper data and a
four-cluster-table-certified Karlsson blow-up lower construction. -/
theorem theorem_one_maximum_from_table_blowup
    (P : TheoremOne.ProblemFamily.{u})
    (h : ExplicitInputs.ConcreteFullyIncrementalTableBlowUpModelSubtheorems P) :
    TheoremOneFinal.TheoremOneStatement P := by
  exact ExplicitInputs.theorem_one_statement_proven_from_concrete_table_blowup_model P h

/-- Manuscript Theorem 1 in displayed formula form from concrete upper data
and a four-cluster-table-certified Karlsson blow-up lower construction. -/
theorem theorem_one_from_table_blowup
    (P : TheoremOne.MaxProblemFamily.{u})
    (h : ExplicitInputs.MaxConcreteFullyIncrementalTableBlowUpModelSubtheorems P) :
    TheoremOneFormulaStatement P := by
  exact ExplicitInputs.theorem_one_formula_statement_proven_from_concrete_table_blowup_model P h

/-- Single-size displayed formula from concrete upper data and a
four-cluster-table-certified Karlsson blow-up lower construction. -/
theorem theorem_one_at_from_table_blowup
    (P : TheoremOne.MaxProblemFamily.{u})
    (h : ExplicitInputs.MaxConcreteFullyIncrementalTableBlowUpModelSubtheorems P)
    (n : Nat) :
    P.aLop n =
      4 * ((n.choose 2 : Nat) : Rat) + manuscriptS n + (n : Rat) + 1 := by
  exact theorem_one_from_table_blowup P h n

/-- Manuscript Theorem 1 in maximum form from paper-style geometric upper
data and a four-cluster-table-certified Karlsson blow-up lower construction. -/
theorem theorem_one_maximum_from_geometric_data_and_table_blowup
    (P : TheoremOne.ProblemFamily.{u})
    (h : ExplicitInputs.ManuscriptGeometricTableBlowUpDataSubtheorems P) :
    TheoremOneFinal.TheoremOneStatement P := by
  exact ExplicitInputs.theorem_one_statement_proven_from_geometric_data_and_table_blowup P h

/-- Manuscript Theorem 1 in displayed formula form from paper-style
geometric upper data and a four-cluster-table-certified Karlsson blow-up lower
construction. -/
theorem theorem_one_from_geometric_data_and_table_blowup
    (P : TheoremOne.MaxProblemFamily.{u})
    (h : ExplicitInputs.MaxManuscriptGeometricTableBlowUpDataSubtheorems P) :
    TheoremOneFormulaStatement P := by
  exact ExplicitInputs.theorem_one_formula_statement_proven_from_geometric_data_and_table_blowup P h

/-- Single-size displayed formula from paper-style geometric upper data and a
four-cluster-table-certified Karlsson blow-up lower construction. -/
theorem theorem_one_at_from_geometric_data_and_table_blowup
    (P : TheoremOne.MaxProblemFamily.{u})
    (h : ExplicitInputs.MaxManuscriptGeometricTableBlowUpDataSubtheorems P)
    (n : Nat) :
    P.aLop n =
      4 * ((n.choose 2 : Nat) : Rat) + manuscriptS n + (n : Rat) + 1 := by
  exact theorem_one_from_geometric_data_and_table_blowup P h n

/-- Manuscript Theorem 1 in maximum form from primitive coordinate lollipop
records and a named Karlsson blow-up lower construction. -/
theorem theorem_one_maximum_from_primitive_geometry_and_explicit_blowup
    (P : TheoremOne.ProblemFamily.{u})
    (h : PrimitiveGeometry.PrimitiveGeometryAndBlowUpSubtheorems P) :
    TheoremOneFinal.TheoremOneStatement P := by
  exact
    PrimitiveGeometry.theorem_one_statement_proven_from_primitive_geometry_and_blowup
      P h

/-- Manuscript Theorem 1 in displayed formula form from primitive coordinate
lollipop records and a named Karlsson blow-up lower construction. -/
theorem theorem_one_from_primitive_geometry_and_explicit_blowup
    (P : TheoremOne.MaxProblemFamily.{u})
    (h : PrimitiveGeometry.MaxPrimitiveGeometryAndBlowUpSubtheorems P) :
    TheoremOneFormulaStatement P := by
  exact
    PrimitiveGeometry.theorem_one_formula_statement_proven_from_primitive_geometry_and_blowup
      P h

/-- Single-size displayed formula from primitive coordinate lollipop records
and a named Karlsson blow-up lower construction. -/
theorem theorem_one_at_from_primitive_geometry_and_explicit_blowup
    (P : TheoremOne.MaxProblemFamily.{u})
    (h : PrimitiveGeometry.MaxPrimitiveGeometryAndBlowUpSubtheorems P)
    (n : Nat) :
    P.aLop n =
      4 * ((n.choose 2 : Nat) : Rat) + manuscriptS n + (n : Rat) + 1 := by
  exact theorem_one_from_primitive_geometry_and_explicit_blowup P h n

/-- Manuscript Theorem 1 in maximum form from carrier-certified primitive
coordinate lollipop records and a named Karlsson blow-up lower construction. -/
theorem theorem_one_maximum_from_primitive_carrier_geometry_and_explicit_blowup
    (P : TheoremOne.ProblemFamily.{u})
    (h : PrimitiveGeometry.PrimitiveCarrierGeometryAndBlowUpSubtheorems P) :
    TheoremOneFinal.TheoremOneStatement P := by
  exact
    PrimitiveGeometry.theorem_one_statement_proven_from_primitive_carrier_geometry_and_blowup
      P h

/-- Manuscript Theorem 1 in displayed formula form from carrier-certified
primitive coordinate lollipop records and a named Karlsson blow-up lower
construction. -/
theorem theorem_one_from_primitive_carrier_geometry_and_explicit_blowup
    (P : TheoremOne.MaxProblemFamily.{u})
    (h : PrimitiveGeometry.MaxPrimitiveCarrierGeometryAndBlowUpSubtheorems P) :
    TheoremOneFormulaStatement P := by
  exact
    PrimitiveGeometry.theorem_one_formula_statement_proven_from_primitive_carrier_geometry_and_blowup
      P h

/-- Single-size displayed formula from carrier-certified primitive coordinate
lollipop records and a named Karlsson blow-up lower construction. -/
theorem theorem_one_at_from_primitive_carrier_geometry_and_explicit_blowup
    (P : TheoremOne.MaxProblemFamily.{u})
    (h : PrimitiveGeometry.MaxPrimitiveCarrierGeometryAndBlowUpSubtheorems P)
    (n : Nat) :
    P.aLop n =
      4 * ((n.choose 2 : Nat) : Rat) + manuscriptS n + (n : Rat) + 1 := by
  exact theorem_one_from_primitive_carrier_geometry_and_explicit_blowup P h n

/-- Manuscript Theorem 1 in maximum form from primitive coordinate lollipop
records and a four-cluster-table-certified Karlsson blow-up lower
construction. -/
theorem theorem_one_maximum_from_primitive_geometry_and_table_blowup
    (P : TheoremOne.ProblemFamily.{u})
    (h : PrimitiveGeometry.PrimitiveGeometryAndTableBlowUpSubtheorems P) :
    TheoremOneFinal.TheoremOneStatement P := by
  exact
    PrimitiveGeometry.theorem_one_statement_proven_from_primitive_geometry_and_table_blowup
      P h

/-- Manuscript Theorem 1 in displayed formula form from primitive coordinate
lollipop records and a four-cluster-table-certified Karlsson blow-up lower
construction. -/
theorem theorem_one_from_primitive_geometry_and_table_blowup
    (P : TheoremOne.MaxProblemFamily.{u})
    (h : PrimitiveGeometry.MaxPrimitiveGeometryAndTableBlowUpSubtheorems P) :
    TheoremOneFormulaStatement P := by
  exact
    PrimitiveGeometry.theorem_one_formula_statement_proven_from_primitive_geometry_and_table_blowup
      P h

/-- Single-size displayed formula from primitive coordinate lollipop records
and a four-cluster-table-certified Karlsson blow-up lower construction. -/
theorem theorem_one_at_from_primitive_geometry_and_table_blowup
    (P : TheoremOne.MaxProblemFamily.{u})
    (h : PrimitiveGeometry.MaxPrimitiveGeometryAndTableBlowUpSubtheorems P)
    (n : Nat) :
    P.aLop n =
      4 * ((n.choose 2 : Nat) : Rat) + manuscriptS n + (n : Rat) + 1 := by
  exact theorem_one_from_primitive_geometry_and_table_blowup P h n

/-- Manuscript Theorem 1 in maximum form from carrier-certified primitive
coordinate lollipop records and a four-cluster-table-certified Karlsson
blow-up lower construction. -/
theorem theorem_one_maximum_from_primitive_carrier_geometry_and_table_blowup
    (P : TheoremOne.ProblemFamily.{u})
    (h : PrimitiveGeometry.PrimitiveCarrierGeometryAndTableBlowUpSubtheorems P) :
    TheoremOneFinal.TheoremOneStatement P := by
  exact
    PrimitiveGeometry.theorem_one_statement_proven_from_primitive_carrier_geometry_and_table_blowup
      P h

/-- Manuscript Theorem 1 in displayed formula form from carrier-certified
primitive coordinate lollipop records and a four-cluster-table-certified
Karlsson blow-up lower construction. -/
theorem theorem_one_from_primitive_carrier_geometry_and_table_blowup
    (P : TheoremOne.MaxProblemFamily.{u})
    (h : PrimitiveGeometry.MaxPrimitiveCarrierGeometryAndTableBlowUpSubtheorems P) :
    TheoremOneFormulaStatement P := by
  exact
    PrimitiveGeometry.theorem_one_formula_statement_proven_from_primitive_carrier_geometry_and_table_blowup
      P h

/-- Single-size displayed formula from carrier-certified primitive coordinate
lollipop records and a four-cluster-table-certified Karlsson blow-up lower
construction. -/
theorem theorem_one_at_from_primitive_carrier_geometry_and_table_blowup
    (P : TheoremOne.MaxProblemFamily.{u})
    (h : PrimitiveGeometry.MaxPrimitiveCarrierGeometryAndTableBlowUpSubtheorems P)
    (n : Nat) :
    P.aLop n =
      4 * ((n.choose 2 : Nat) : Rat) + manuscriptS n + (n : Rat) + 1 := by
  exact theorem_one_from_primitive_carrier_geometry_and_table_blowup P h n

/-- Manuscript Theorem 1 in maximum form from concrete upper data and a
clustered Karlsson blow-up lower construction. -/
theorem theorem_one_maximum_from_clustered_blowup
    (P : TheoremOne.ProblemFamily.{u})
    (h : ExplicitInputs.ConcreteFullyIncrementalClusteredBlowUpModelSubtheorems P) :
    TheoremOneFinal.TheoremOneStatement P := by
  exact ExplicitInputs.theorem_one_statement_proven_from_concrete_clustered_blowup_model P h

/-- Manuscript Theorem 1 in displayed formula form from concrete upper data
and a clustered Karlsson blow-up lower construction. -/
theorem theorem_one_from_clustered_blowup
    (P : TheoremOne.MaxProblemFamily.{u})
    (h : ExplicitInputs.MaxConcreteFullyIncrementalClusteredBlowUpModelSubtheorems P) :
    TheoremOneFormulaStatement P := by
  exact ExplicitInputs.theorem_one_formula_statement_proven_from_concrete_clustered_blowup_model P h

/-- Single-size displayed formula from concrete upper data and a clustered
Karlsson blow-up lower construction. -/
theorem theorem_one_at_from_clustered_blowup
    (P : TheoremOne.MaxProblemFamily.{u})
    (h : ExplicitInputs.MaxConcreteFullyIncrementalClusteredBlowUpModelSubtheorems P)
    (n : Nat) :
    P.aLop n =
      4 * ((n.choose 2 : Nat) : Rat) + manuscriptS n + (n : Rat) + 1 := by
  exact theorem_one_from_clustered_blowup P h n

/-- Manuscript Theorem 1 in maximum form from paper-style geometric upper
data and a clustered Karlsson blow-up lower construction. -/
theorem theorem_one_maximum_from_geometric_data_and_clustered_blowup
    (P : TheoremOne.ProblemFamily.{u})
    (h : ExplicitInputs.ManuscriptGeometricClusteredBlowUpDataSubtheorems P) :
    TheoremOneFinal.TheoremOneStatement P := by
  exact ExplicitInputs.theorem_one_statement_proven_from_geometric_data_and_clustered_blowup P h

/-- Manuscript Theorem 1 in displayed formula form from paper-style geometric
upper data and a clustered Karlsson blow-up lower construction. -/
theorem theorem_one_from_geometric_data_and_clustered_blowup
    (P : TheoremOne.MaxProblemFamily.{u})
    (h : ExplicitInputs.MaxManuscriptGeometricClusteredBlowUpDataSubtheorems P) :
    TheoremOneFormulaStatement P := by
  exact ExplicitInputs.theorem_one_formula_statement_proven_from_geometric_data_and_clustered_blowup P h

/-- Single-size displayed formula from paper-style geometric upper data and a
clustered Karlsson blow-up lower construction. -/
theorem theorem_one_at_from_geometric_data_and_clustered_blowup
    (P : TheoremOne.MaxProblemFamily.{u})
    (h : ExplicitInputs.MaxManuscriptGeometricClusteredBlowUpDataSubtheorems P)
    (n : Nat) :
    P.aLop n =
      4 * ((n.choose 2 : Nat) : Rat) + manuscriptS n + (n : Rat) + 1 := by
  exact theorem_one_from_geometric_data_and_clustered_blowup P h n

/-- Manuscript Theorem 1 in maximum form from primitive coordinate lollipop
records and a clustered Karlsson blow-up lower construction. -/
theorem theorem_one_maximum_from_primitive_geometry_and_clustered_blowup
    (P : TheoremOne.ProblemFamily.{u})
    (h : PrimitiveGeometry.PrimitiveGeometryAndClusteredBlowUpSubtheorems P) :
    TheoremOneFinal.TheoremOneStatement P := by
  exact
    PrimitiveGeometry.theorem_one_statement_proven_from_primitive_geometry_and_clustered_blowup
      P h

/-- Manuscript Theorem 1 in displayed formula form from primitive coordinate
lollipop records and a clustered Karlsson blow-up lower construction. -/
theorem theorem_one_from_primitive_geometry_and_clustered_blowup
    (P : TheoremOne.MaxProblemFamily.{u})
    (h : PrimitiveGeometry.MaxPrimitiveGeometryAndClusteredBlowUpSubtheorems P) :
    TheoremOneFormulaStatement P := by
  exact
    PrimitiveGeometry.theorem_one_formula_statement_proven_from_primitive_geometry_and_clustered_blowup
      P h

/-- Single-size displayed formula from primitive coordinate lollipop records
and a clustered Karlsson blow-up lower construction. -/
theorem theorem_one_at_from_primitive_geometry_and_clustered_blowup
    (P : TheoremOne.MaxProblemFamily.{u})
    (h : PrimitiveGeometry.MaxPrimitiveGeometryAndClusteredBlowUpSubtheorems P)
    (n : Nat) :
    P.aLop n =
      4 * ((n.choose 2 : Nat) : Rat) + manuscriptS n + (n : Rat) + 1 := by
  exact theorem_one_from_primitive_geometry_and_clustered_blowup P h n

/-- Manuscript Theorem 1 in maximum form from carrier-certified primitive
coordinate lollipop records and a clustered Karlsson blow-up lower
construction. -/
theorem theorem_one_maximum_from_primitive_carrier_geometry_and_clustered_blowup
    (P : TheoremOne.ProblemFamily.{u})
    (h : PrimitiveGeometry.PrimitiveCarrierGeometryAndClusteredBlowUpSubtheorems P) :
    TheoremOneFinal.TheoremOneStatement P := by
  exact
    PrimitiveGeometry.theorem_one_statement_proven_from_primitive_carrier_geometry_and_clustered_blowup
      P h

/-- Manuscript Theorem 1 in displayed formula form from carrier-certified
primitive coordinate lollipop records and a clustered Karlsson blow-up lower
construction. -/
theorem theorem_one_from_primitive_carrier_geometry_and_clustered_blowup
    (P : TheoremOne.MaxProblemFamily.{u})
    (h : PrimitiveGeometry.MaxPrimitiveCarrierGeometryAndClusteredBlowUpSubtheorems P) :
    TheoremOneFormulaStatement P := by
  exact
    PrimitiveGeometry.theorem_one_formula_statement_proven_from_primitive_carrier_geometry_and_clustered_blowup
      P h

/-- Single-size displayed formula from carrier-certified primitive coordinate
lollipop records and a clustered Karlsson blow-up lower construction. -/
theorem theorem_one_at_from_primitive_carrier_geometry_and_clustered_blowup
    (P : TheoremOne.MaxProblemFamily.{u})
    (h : PrimitiveGeometry.MaxPrimitiveCarrierGeometryAndClusteredBlowUpSubtheorems P)
    (n : Nat) :
    P.aLop n =
      4 * ((n.choose 2 : Nat) : Rat) + manuscriptS n + (n : Rat) + 1 := by
  exact theorem_one_from_primitive_carrier_geometry_and_clustered_blowup P h n

end TheoremOneManuscript
end Lollipop
