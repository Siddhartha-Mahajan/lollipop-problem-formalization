import Lollipop.Internal.Manuscript.Formalization.CardinalityClusteredBridge

/-!
Manuscript Theorem 1 as a statement proved from named subtheorem packages.

This file is intentionally small and theorem-facing.  The finite lower
counting step routes through the cardinality-clustered formalization: for each
sorted quadruple Lean builds the canonical four-fiber cluster map, proves the
same/inter-cluster pair counts from finite cardinalities, collapses the pair
sum to Karlsson's table, and then invokes the existing upper/lower theorem
stack.
-/

namespace Lollipop
namespace TheoremOneManuscript

universe u

/-- Theorem 1 in the manuscript's displayed formula form. -/
abbrev TheoremOneStatement (P : TheoremOne.MaxProblemFamily.{u}) : Prop :=
  TheoremOneFormulaStatement P

/-- The concrete subtheorem package: exact incremental upper geometry plus
named incremental Karlsson blow-up lower data. -/
abbrev ConcreteTheoremOneSubtheorems
    (P : TheoremOne.MaxProblemFamily.{u}) : Type u :=
  ExplicitInputs.MaxConcreteFullyIncrementalBlowUpModelSubtheorems P

/-- The paper-style geometric subtheorem package: global upper geometry plus
named incremental Karlsson blow-up lower data. -/
abbrev GeometricTheoremOneSubtheorems
    (P : TheoremOne.MaxProblemFamily.{u}) : Type u :=
  ExplicitInputs.MaxManuscriptGeometricBlowUpDataSubtheorems P

/-- The primitive-coordinate subtheorem package. -/
abbrev PrimitiveTheoremOneSubtheorems
    (P : TheoremOne.MaxProblemFamily.{u}) : Type u :=
  PrimitiveGeometry.MaxPrimitiveGeometryAndBlowUpSubtheorems P

/-- The carrier-certified primitive-coordinate subtheorem package. -/
abbrev PrimitiveCarrierTheoremOneSubtheorems
    (P : TheoremOne.MaxProblemFamily.{u}) : Type u :=
  PrimitiveGeometry.MaxPrimitiveCarrierGeometryAndBlowUpSubtheorems P

/-- Theorem 1 from the concrete named subtheorems, with finite lower counting
proved via the canonical cardinality-clustered layer. -/
theorem theorem_one_from_concrete_subtheorems
    (P : TheoremOne.MaxProblemFamily.{u})
    (h : ConcreteTheoremOneSubtheorems P) :
    TheoremOneStatement P := by
  exact theorem_one_from_cardinality_clustered_blowup P
    h.toConcreteFullyIncrementalCardinalityClusteredBlowUpModelSubtheorems

/-- Single-size form of Theorem 1 from the concrete named subtheorems. -/
theorem theorem_one_at_from_concrete_subtheorems
    (P : TheoremOne.MaxProblemFamily.{u})
    (h : ConcreteTheoremOneSubtheorems P)
    (n : Nat) :
    P.aLop n =
      4 * ((n.choose 2 : Nat) : Rat) + manuscriptS n + (n : Rat) + 1 := by
  exact theorem_one_from_concrete_subtheorems P h n

/-- Theorem 1 from the paper-style geometric named subtheorems, with finite
lower counting proved via the canonical cardinality-clustered layer. -/
theorem theorem_one_from_geometric_subtheorems
    (P : TheoremOne.MaxProblemFamily.{u})
    (h : GeometricTheoremOneSubtheorems P) :
    TheoremOneStatement P := by
  exact theorem_one_from_geometric_data_and_cardinality_clustered_blowup P
    h.toManuscriptGeometricCardinalityClusteredBlowUpDataSubtheorems

/-- Single-size form of Theorem 1 from the paper-style geometric named
subtheorems. -/
theorem theorem_one_at_from_geometric_subtheorems
    (P : TheoremOne.MaxProblemFamily.{u})
    (h : GeometricTheoremOneSubtheorems P)
    (n : Nat) :
    P.aLop n =
      4 * ((n.choose 2 : Nat) : Rat) + manuscriptS n + (n : Rat) + 1 := by
  exact theorem_one_from_geometric_subtheorems P h n

/-- Theorem 1 from primitive-coordinate subtheorems, with finite lower
counting proved via the canonical cardinality-clustered layer. -/
theorem theorem_one_from_primitive_subtheorems
    (P : TheoremOne.MaxProblemFamily.{u})
    (h : PrimitiveTheoremOneSubtheorems P) :
    TheoremOneStatement P := by
  exact theorem_one_from_primitive_geometry_and_cardinality_clustered_blowup P
    h.toPrimitiveGeometryAndCardinalityClusteredBlowUpSubtheorems

/-- Single-size form of Theorem 1 from primitive-coordinate subtheorems. -/
theorem theorem_one_at_from_primitive_subtheorems
    (P : TheoremOne.MaxProblemFamily.{u})
    (h : PrimitiveTheoremOneSubtheorems P)
    (n : Nat) :
    P.aLop n =
      4 * ((n.choose 2 : Nat) : Rat) + manuscriptS n + (n : Rat) + 1 := by
  exact theorem_one_from_primitive_subtheorems P h n

/-- Theorem 1 from carrier-certified primitive-coordinate subtheorems, with
finite lower counting proved via the canonical cardinality-clustered layer. -/
theorem theorem_one_from_primitive_carrier_subtheorems
    (P : TheoremOne.MaxProblemFamily.{u})
    (h : PrimitiveCarrierTheoremOneSubtheorems P) :
    TheoremOneStatement P := by
  exact
    theorem_one_from_primitive_carrier_geometry_and_cardinality_clustered_blowup
      P h.toPrimitiveCarrierGeometryAndCardinalityClusteredBlowUpSubtheorems

/-- Single-size form of Theorem 1 from carrier-certified primitive-coordinate
subtheorems. -/
theorem theorem_one_at_from_primitive_carrier_subtheorems
    (P : TheoremOne.MaxProblemFamily.{u})
    (h : PrimitiveCarrierTheoremOneSubtheorems P)
    (n : Nat) :
    P.aLop n =
      4 * ((n.choose 2 : Nat) : Rat) + manuscriptS n + (n : Rat) + 1 := by
  exact theorem_one_from_primitive_carrier_subtheorems P h n

end TheoremOneManuscript
end Lollipop
