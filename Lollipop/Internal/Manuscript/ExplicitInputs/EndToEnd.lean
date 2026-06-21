import Lollipop.Internal.Manuscript.ExplicitInputs.ClusteredLower
import Lollipop.Internal.Manuscript.GeometricInputs

/-!
End-to-end manuscript endpoints from explicit lower-construction data.

This module is deliberately separate from the earlier manuscript files.  It
keeps the previously checked interfaces unchanged and adds stronger final
packages whose lower side is a named Karlsson blow-up construction for every
sorted quadruple, not merely an existential realization relation.
-/

namespace Lollipop
namespace TheoremOneManuscript
namespace ExplicitInputs

universe u

/-- Fully incremental concrete model data with a named Karlsson blow-up lower
construction. -/
structure ConcreteFullyIncrementalBlowUpModelSubtheorems
    (P : TheoremOne.ProblemFamily.{u}) where
  upper_geometry : CanonicalExactUpperGeometryIncrementalData P
  lower_karlsson : KarlssonBlowUpIncrementalLowerData P

namespace ConcreteFullyIncrementalBlowUpModelSubtheorems

/-- Convert the stronger named-blow-up package to the existing fully
incremental concrete package. -/
def toConcreteFullyIncrementalModelSubtheorems
    {P : TheoremOne.ProblemFamily.{u}}
    (h : ConcreteFullyIncrementalBlowUpModelSubtheorems P) :
    ConcreteFullyIncrementalModelSubtheorems P where
  upper_geometry := h.upper_geometry
  lower_karlsson := h.lower_karlsson.toSortedKarlssonIncrementalLowerData

end ConcreteFullyIncrementalBlowUpModelSubtheorems

/-- Paper-style global geometric data with a named Karlsson blow-up lower
construction. -/
structure ManuscriptGeometricBlowUpDataSubtheorems
    (P : TheoremOne.ProblemFamily.{u}) where
  upper_geometry : ManuscriptGeometricIncrementalUpperData P
  lower_karlsson : KarlssonBlowUpIncrementalLowerData P

namespace ManuscriptGeometricBlowUpDataSubtheorems

/-- Convert the stronger named-blow-up package to the existing fully
incremental paper-style geometric package. -/
noncomputable def toManuscriptGeometricFullyIncrementalDataSubtheorems
    {P : TheoremOne.ProblemFamily.{u}}
    (h : ManuscriptGeometricBlowUpDataSubtheorems P) :
    ManuscriptGeometricFullyIncrementalDataSubtheorems P where
  upper_geometry := h.upper_geometry
  lower_karlsson := h.lower_karlsson.toSortedKarlssonIncrementalLowerData

end ManuscriptGeometricBlowUpDataSubtheorems

/-- Fully incremental concrete model data whose lower construction is
certified by the explicit four-cluster Karlsson table. -/
structure ConcreteFullyIncrementalTableBlowUpModelSubtheorems
    (P : TheoremOne.ProblemFamily.{u}) where
  upper_geometry : CanonicalExactUpperGeometryIncrementalData P
  lower_karlsson : KarlssonTableBlowUpIncrementalLowerData P

namespace ConcreteFullyIncrementalTableBlowUpModelSubtheorems

/-- Convert table-shaped lower data to the named-blow-up package after Lean
derives `lowerCrossingsOfQuad` from the table sum. -/
def toConcreteFullyIncrementalBlowUpModelSubtheorems
    {P : TheoremOne.ProblemFamily.{u}}
    (h : ConcreteFullyIncrementalTableBlowUpModelSubtheorems P) :
    ConcreteFullyIncrementalBlowUpModelSubtheorems P where
  upper_geometry := h.upper_geometry
  lower_karlsson := h.lower_karlsson.toKarlssonBlowUpIncrementalLowerData

end ConcreteFullyIncrementalTableBlowUpModelSubtheorems

/-- Paper-style global geometric data whose lower construction is certified
by the explicit four-cluster Karlsson table. -/
structure ManuscriptGeometricTableBlowUpDataSubtheorems
    (P : TheoremOne.ProblemFamily.{u}) where
  upper_geometry : ManuscriptGeometricIncrementalUpperData P
  lower_karlsson : KarlssonTableBlowUpIncrementalLowerData P

namespace ManuscriptGeometricTableBlowUpDataSubtheorems

/-- Convert table-shaped lower data to the named-blow-up paper-style package
after Lean derives `lowerCrossingsOfQuad` from the table sum. -/
def toManuscriptGeometricBlowUpDataSubtheorems
    {P : TheoremOne.ProblemFamily.{u}}
    (h : ManuscriptGeometricTableBlowUpDataSubtheorems P) :
    ManuscriptGeometricBlowUpDataSubtheorems P where
  upper_geometry := h.upper_geometry
  lower_karlsson := h.lower_karlsson.toKarlssonBlowUpIncrementalLowerData

end ManuscriptGeometricTableBlowUpDataSubtheorems

/-- Fully incremental concrete model data whose lower construction carries an
individual cluster map on the produced lollipops. -/
structure ConcreteFullyIncrementalClusteredBlowUpModelSubtheorems
    (P : TheoremOne.ProblemFamily.{u}) where
  upper_geometry : CanonicalExactUpperGeometryIncrementalData P
  lower_karlsson : ClusteredKarlssonBlowUpIncrementalLowerData P

namespace ConcreteFullyIncrementalClusteredBlowUpModelSubtheorems

/-- Convert clustered lower data to table-certified lower data after Lean
collapses the individual pair table to the four-cluster table. -/
def toConcreteFullyIncrementalTableBlowUpModelSubtheorems
    {P : TheoremOne.ProblemFamily.{u}}
    (h : ConcreteFullyIncrementalClusteredBlowUpModelSubtheorems P) :
    ConcreteFullyIncrementalTableBlowUpModelSubtheorems P where
  upper_geometry := h.upper_geometry
  lower_karlsson := h.lower_karlsson.toKarlssonTableBlowUpIncrementalLowerData

end ConcreteFullyIncrementalClusteredBlowUpModelSubtheorems

/-- Paper-style global geometric data whose lower construction carries an
individual cluster map on the produced lollipops. -/
structure ManuscriptGeometricClusteredBlowUpDataSubtheorems
    (P : TheoremOne.ProblemFamily.{u}) where
  upper_geometry : ManuscriptGeometricIncrementalUpperData P
  lower_karlsson : ClusteredKarlssonBlowUpIncrementalLowerData P

namespace ManuscriptGeometricClusteredBlowUpDataSubtheorems

/-- Convert clustered lower data to table-certified paper-style lower data. -/
def toManuscriptGeometricTableBlowUpDataSubtheorems
    {P : TheoremOne.ProblemFamily.{u}}
    (h : ManuscriptGeometricClusteredBlowUpDataSubtheorems P) :
    ManuscriptGeometricTableBlowUpDataSubtheorems P where
  upper_geometry := h.upper_geometry
  lower_karlsson := h.lower_karlsson.toKarlssonTableBlowUpIncrementalLowerData

end ManuscriptGeometricClusteredBlowUpDataSubtheorems

/-- Maximum-form Theorem 1 from concrete upper data and a named Karlsson
blow-up lower construction. -/
theorem theorem_one_statement_proven_from_concrete_blowup_model
    (P : TheoremOne.ProblemFamily.{u})
    (h : ConcreteFullyIncrementalBlowUpModelSubtheorems P) :
    TheoremOneFinal.TheoremOneStatement P := by
  exact theorem_one_statement_proven_from_fully_incremental_concrete_model
    P h.toConcreteFullyIncrementalModelSubtheorems

/-- Maximum-form Theorem 1 from paper-style geometric upper data and a named
Karlsson blow-up lower construction. -/
theorem theorem_one_statement_proven_from_geometric_data_and_blowup
    (P : TheoremOne.ProblemFamily.{u})
    (h : ManuscriptGeometricBlowUpDataSubtheorems P) :
    TheoremOneFinal.TheoremOneStatement P := by
  exact theorem_one_statement_proven_from_manuscript_geometric_fully_incremental_data
    P h.toManuscriptGeometricFullyIncrementalDataSubtheorems

/-- Maximum-form Theorem 1 from concrete upper data and a table-certified
Karlsson blow-up lower construction. -/
theorem theorem_one_statement_proven_from_concrete_table_blowup_model
    (P : TheoremOne.ProblemFamily.{u})
    (h : ConcreteFullyIncrementalTableBlowUpModelSubtheorems P) :
    TheoremOneFinal.TheoremOneStatement P := by
  exact theorem_one_statement_proven_from_concrete_blowup_model
    P h.toConcreteFullyIncrementalBlowUpModelSubtheorems

/-- Maximum-form Theorem 1 from paper-style geometric upper data and a
table-certified Karlsson blow-up lower construction. -/
theorem theorem_one_statement_proven_from_geometric_data_and_table_blowup
    (P : TheoremOne.ProblemFamily.{u})
    (h : ManuscriptGeometricTableBlowUpDataSubtheorems P) :
    TheoremOneFinal.TheoremOneStatement P := by
  exact theorem_one_statement_proven_from_geometric_data_and_blowup
    P h.toManuscriptGeometricBlowUpDataSubtheorems

/-- Maximum-form Theorem 1 from concrete upper data and a clustered Karlsson
blow-up lower construction. -/
theorem theorem_one_statement_proven_from_concrete_clustered_blowup_model
    (P : TheoremOne.ProblemFamily.{u})
    (h : ConcreteFullyIncrementalClusteredBlowUpModelSubtheorems P) :
    TheoremOneFinal.TheoremOneStatement P := by
  exact theorem_one_statement_proven_from_concrete_table_blowup_model
    P h.toConcreteFullyIncrementalTableBlowUpModelSubtheorems

/-- Maximum-form Theorem 1 from paper-style geometric upper data and a
clustered Karlsson blow-up lower construction. -/
theorem theorem_one_statement_proven_from_geometric_data_and_clustered_blowup
    (P : TheoremOne.ProblemFamily.{u})
    (h : ManuscriptGeometricClusteredBlowUpDataSubtheorems P) :
    TheoremOneFinal.TheoremOneStatement P := by
  exact theorem_one_statement_proven_from_geometric_data_and_table_blowup
    P h.toManuscriptGeometricTableBlowUpDataSubtheorems

/-- Concrete named-blow-up obligations for a family with a named maximum
count function. -/
def MaxConcreteFullyIncrementalBlowUpModelSubtheorems
    (P : TheoremOne.MaxProblemFamily.{u}) : Type u :=
  ConcreteFullyIncrementalBlowUpModelSubtheorems P.toProblemFamily

/-- Paper-style geometric named-blow-up obligations for a family with a named
maximum count function. -/
def MaxManuscriptGeometricBlowUpDataSubtheorems
    (P : TheoremOne.MaxProblemFamily.{u}) : Type u :=
  ManuscriptGeometricBlowUpDataSubtheorems P.toProblemFamily

/-- Concrete table-certified named-blow-up obligations for a family with a
named maximum count function. -/
def MaxConcreteFullyIncrementalTableBlowUpModelSubtheorems
    (P : TheoremOne.MaxProblemFamily.{u}) : Type u :=
  ConcreteFullyIncrementalTableBlowUpModelSubtheorems P.toProblemFamily

/-- Paper-style geometric table-certified named-blow-up obligations for a
family with a named maximum count function. -/
def MaxManuscriptGeometricTableBlowUpDataSubtheorems
    (P : TheoremOne.MaxProblemFamily.{u}) : Type u :=
  ManuscriptGeometricTableBlowUpDataSubtheorems P.toProblemFamily

/-- Concrete clustered named-blow-up obligations for a family with a named
maximum count function. -/
def MaxConcreteFullyIncrementalClusteredBlowUpModelSubtheorems
    (P : TheoremOne.MaxProblemFamily.{u}) : Type u :=
  ConcreteFullyIncrementalClusteredBlowUpModelSubtheorems P.toProblemFamily

/-- Paper-style geometric clustered named-blow-up obligations for a family
with a named maximum count function. -/
def MaxManuscriptGeometricClusteredBlowUpDataSubtheorems
    (P : TheoremOne.MaxProblemFamily.{u}) : Type u :=
  ManuscriptGeometricClusteredBlowUpDataSubtheorems P.toProblemFamily

/-- Formula-form Theorem 1 from concrete upper data and a named Karlsson
blow-up lower construction. -/
theorem theorem_one_formula_statement_proven_from_concrete_blowup_model
    (P : TheoremOne.MaxProblemFamily.{u})
    (h : MaxConcreteFullyIncrementalBlowUpModelSubtheorems P) :
    TheoremOneFormulaStatement P := by
  exact theorem_one_formula_statement_proven_from_fully_incremental_concrete_model
    P h.toConcreteFullyIncrementalModelSubtheorems

/-- Formula-form Theorem 1 from paper-style geometric upper data and a named
Karlsson blow-up lower construction. -/
theorem theorem_one_formula_statement_proven_from_geometric_data_and_blowup
    (P : TheoremOne.MaxProblemFamily.{u})
    (h : MaxManuscriptGeometricBlowUpDataSubtheorems P) :
    TheoremOneFormulaStatement P := by
  exact theorem_one_formula_statement_proven_from_manuscript_geometric_fully_incremental_data
    P h.toManuscriptGeometricFullyIncrementalDataSubtheorems

/-- Formula-form Theorem 1 from concrete upper data and a table-certified
Karlsson blow-up lower construction. -/
theorem theorem_one_formula_statement_proven_from_concrete_table_blowup_model
    (P : TheoremOne.MaxProblemFamily.{u})
    (h : MaxConcreteFullyIncrementalTableBlowUpModelSubtheorems P) :
    TheoremOneFormulaStatement P := by
  exact theorem_one_formula_statement_proven_from_concrete_blowup_model
    P h.toConcreteFullyIncrementalBlowUpModelSubtheorems

/-- Formula-form Theorem 1 from paper-style geometric upper data and a
table-certified Karlsson blow-up lower construction. -/
theorem theorem_one_formula_statement_proven_from_geometric_data_and_table_blowup
    (P : TheoremOne.MaxProblemFamily.{u})
    (h : MaxManuscriptGeometricTableBlowUpDataSubtheorems P) :
    TheoremOneFormulaStatement P := by
  exact theorem_one_formula_statement_proven_from_geometric_data_and_blowup
    P h.toManuscriptGeometricBlowUpDataSubtheorems

/-- Formula-form Theorem 1 from concrete upper data and a clustered Karlsson
blow-up lower construction. -/
theorem theorem_one_formula_statement_proven_from_concrete_clustered_blowup_model
    (P : TheoremOne.MaxProblemFamily.{u})
    (h : MaxConcreteFullyIncrementalClusteredBlowUpModelSubtheorems P) :
    TheoremOneFormulaStatement P := by
  exact theorem_one_formula_statement_proven_from_concrete_table_blowup_model
    P h.toConcreteFullyIncrementalTableBlowUpModelSubtheorems

/-- Formula-form Theorem 1 from paper-style geometric upper data and a
clustered Karlsson blow-up lower construction. -/
theorem theorem_one_formula_statement_proven_from_geometric_data_and_clustered_blowup
    (P : TheoremOne.MaxProblemFamily.{u})
    (h : MaxManuscriptGeometricClusteredBlowUpDataSubtheorems P) :
    TheoremOneFormulaStatement P := by
  exact theorem_one_formula_statement_proven_from_geometric_data_and_table_blowup
    P h.toManuscriptGeometricTableBlowUpDataSubtheorems

/-- Single-size displayed formula from concrete upper data and a named
Karlsson blow-up lower construction. -/
theorem theorem_one_formula_at_proven_from_concrete_blowup_model
    (P : TheoremOne.MaxProblemFamily.{u})
    (h : MaxConcreteFullyIncrementalBlowUpModelSubtheorems P)
    (n : Nat) :
    P.aLop n =
      4 * ((n.choose 2 : Nat) : Rat) + manuscriptS n + (n : Rat) + 1 := by
  exact theorem_one_formula_statement_proven_from_concrete_blowup_model P h n

/-- Single-size displayed formula from paper-style geometric upper data and a
named Karlsson blow-up lower construction. -/
theorem theorem_one_formula_at_proven_from_geometric_data_and_blowup
    (P : TheoremOne.MaxProblemFamily.{u})
    (h : MaxManuscriptGeometricBlowUpDataSubtheorems P)
    (n : Nat) :
    P.aLop n =
      4 * ((n.choose 2 : Nat) : Rat) + manuscriptS n + (n : Rat) + 1 := by
  exact theorem_one_formula_statement_proven_from_geometric_data_and_blowup P h n

/-- Single-size displayed formula from concrete upper data and a
table-certified Karlsson blow-up lower construction. -/
theorem theorem_one_formula_at_proven_from_concrete_table_blowup_model
    (P : TheoremOne.MaxProblemFamily.{u})
    (h : MaxConcreteFullyIncrementalTableBlowUpModelSubtheorems P)
    (n : Nat) :
    P.aLop n =
      4 * ((n.choose 2 : Nat) : Rat) + manuscriptS n + (n : Rat) + 1 := by
  exact theorem_one_formula_statement_proven_from_concrete_table_blowup_model P h n

/-- Single-size displayed formula from paper-style geometric upper data and a
table-certified Karlsson blow-up lower construction. -/
theorem theorem_one_formula_at_proven_from_geometric_data_and_table_blowup
    (P : TheoremOne.MaxProblemFamily.{u})
    (h : MaxManuscriptGeometricTableBlowUpDataSubtheorems P)
    (n : Nat) :
    P.aLop n =
      4 * ((n.choose 2 : Nat) : Rat) + manuscriptS n + (n : Rat) + 1 := by
  exact theorem_one_formula_statement_proven_from_geometric_data_and_table_blowup P h n

/-- Single-size displayed formula from concrete upper data and a clustered
Karlsson blow-up lower construction. -/
theorem theorem_one_formula_at_proven_from_concrete_clustered_blowup_model
    (P : TheoremOne.MaxProblemFamily.{u})
    (h : MaxConcreteFullyIncrementalClusteredBlowUpModelSubtheorems P)
    (n : Nat) :
    P.aLop n =
      4 * ((n.choose 2 : Nat) : Rat) + manuscriptS n + (n : Rat) + 1 := by
  exact theorem_one_formula_statement_proven_from_concrete_clustered_blowup_model P h n

/-- Single-size displayed formula from paper-style geometric upper data and a
clustered Karlsson blow-up lower construction. -/
theorem theorem_one_formula_at_proven_from_geometric_data_and_clustered_blowup
    (P : TheoremOne.MaxProblemFamily.{u})
    (h : MaxManuscriptGeometricClusteredBlowUpDataSubtheorems P)
    (n : Nat) :
    P.aLop n =
      4 * ((n.choose 2 : Nat) : Rat) + manuscriptS n + (n : Rat) + 1 := by
  exact theorem_one_formula_statement_proven_from_geometric_data_and_clustered_blowup P h n

end ExplicitInputs
end TheoremOneManuscript
end Lollipop
