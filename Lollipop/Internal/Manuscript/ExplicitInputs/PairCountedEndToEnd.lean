import Lollipop.Internal.Manuscript.ExplicitInputs.EndToEnd
import Lollipop.Internal.Manuscript.ExplicitInputs.PairCountedClusteredLower

/-!
Theorem 1 endpoints from pair-counted clustered lower data.

This module is a non-disruptive strengthening of `ExplicitInputs.EndToEnd`.
The lower side no longer supplies the final collapse from individual
cluster-pair crossings to the four-cluster table directly.  It supplies finite
same/inter-cluster pair counts; `PairCountedClusteredLower.lean` proves the
collapse and then this file reuses the existing theorem stack.
-/

namespace Lollipop
namespace TheoremOneManuscript
namespace ExplicitInputs

universe u

/-- Fully incremental concrete model data whose lower construction is
certified by explicit finite same/inter-cluster pair counts. -/
structure ConcreteFullyIncrementalPairCountedClusteredBlowUpModelSubtheorems
    (P : TheoremOne.ProblemFamily.{u}) where
  upper_geometry : CanonicalExactUpperGeometryIncrementalData P
  lower_karlsson : PairCountedClusteredKarlssonBlowUpIncrementalLowerData P

namespace ConcreteFullyIncrementalPairCountedClusteredBlowUpModelSubtheorems

def toConcreteFullyIncrementalClusteredBlowUpModelSubtheorems
    {P : TheoremOne.ProblemFamily.{u}}
    (h : ConcreteFullyIncrementalPairCountedClusteredBlowUpModelSubtheorems P) :
    ConcreteFullyIncrementalClusteredBlowUpModelSubtheorems P where
  upper_geometry := h.upper_geometry
  lower_karlsson := h.lower_karlsson.toClusteredKarlssonBlowUpIncrementalLowerData

end ConcreteFullyIncrementalPairCountedClusteredBlowUpModelSubtheorems

/-- Paper-style global geometric data whose lower construction is certified by
explicit finite same/inter-cluster pair counts. -/
structure ManuscriptGeometricPairCountedClusteredBlowUpDataSubtheorems
    (P : TheoremOne.ProblemFamily.{u}) where
  upper_geometry : ManuscriptGeometricIncrementalUpperData P
  lower_karlsson : PairCountedClusteredKarlssonBlowUpIncrementalLowerData P

namespace ManuscriptGeometricPairCountedClusteredBlowUpDataSubtheorems

def toManuscriptGeometricClusteredBlowUpDataSubtheorems
    {P : TheoremOne.ProblemFamily.{u}}
    (h : ManuscriptGeometricPairCountedClusteredBlowUpDataSubtheorems P) :
    ManuscriptGeometricClusteredBlowUpDataSubtheorems P where
  upper_geometry := h.upper_geometry
  lower_karlsson := h.lower_karlsson.toClusteredKarlssonBlowUpIncrementalLowerData

end ManuscriptGeometricPairCountedClusteredBlowUpDataSubtheorems

/-- Fully incremental concrete model data whose lower construction supplies
cluster fiber cardinalities and the six inter-cluster pair counts; same-cluster
pair counts are derived in Lean. -/
structure ConcreteFullyIncrementalFiberCountedClusteredBlowUpModelSubtheorems
    (P : TheoremOne.ProblemFamily.{u}) where
  upper_geometry : CanonicalExactUpperGeometryIncrementalData P
  lower_karlsson : FiberCountedClusteredKarlssonBlowUpIncrementalLowerData P

namespace ConcreteFullyIncrementalFiberCountedClusteredBlowUpModelSubtheorems

def toConcreteFullyIncrementalPairCountedClusteredBlowUpModelSubtheorems
    {P : TheoremOne.ProblemFamily.{u}}
    (h : ConcreteFullyIncrementalFiberCountedClusteredBlowUpModelSubtheorems P) :
    ConcreteFullyIncrementalPairCountedClusteredBlowUpModelSubtheorems P where
  upper_geometry := h.upper_geometry
  lower_karlsson :=
    h.lower_karlsson.toPairCountedClusteredKarlssonBlowUpIncrementalLowerData

end ConcreteFullyIncrementalFiberCountedClusteredBlowUpModelSubtheorems

/-- Paper-style global geometric data whose lower construction supplies
cluster fiber cardinalities and the six inter-cluster pair counts. -/
structure ManuscriptGeometricFiberCountedClusteredBlowUpDataSubtheorems
    (P : TheoremOne.ProblemFamily.{u}) where
  upper_geometry : ManuscriptGeometricIncrementalUpperData P
  lower_karlsson : FiberCountedClusteredKarlssonBlowUpIncrementalLowerData P

namespace ManuscriptGeometricFiberCountedClusteredBlowUpDataSubtheorems

def toManuscriptGeometricPairCountedClusteredBlowUpDataSubtheorems
    {P : TheoremOne.ProblemFamily.{u}}
    (h : ManuscriptGeometricFiberCountedClusteredBlowUpDataSubtheorems P) :
    ManuscriptGeometricPairCountedClusteredBlowUpDataSubtheorems P where
  upper_geometry := h.upper_geometry
  lower_karlsson :=
    h.lower_karlsson.toPairCountedClusteredKarlssonBlowUpIncrementalLowerData

end ManuscriptGeometricFiberCountedClusteredBlowUpDataSubtheorems

/-- Fully incremental concrete model data whose lower construction supplies
only cluster fiber cardinalities for the finite counting part. -/
structure ConcreteFullyIncrementalCardinalityClusteredBlowUpModelSubtheorems
    (P : TheoremOne.ProblemFamily.{u}) where
  upper_geometry : CanonicalExactUpperGeometryIncrementalData P
  lower_karlsson : CardinalityClusteredKarlssonBlowUpIncrementalLowerData P

namespace ConcreteFullyIncrementalCardinalityClusteredBlowUpModelSubtheorems

def toConcreteFullyIncrementalFiberCountedClusteredBlowUpModelSubtheorems
    {P : TheoremOne.ProblemFamily.{u}}
    (h : ConcreteFullyIncrementalCardinalityClusteredBlowUpModelSubtheorems P) :
    ConcreteFullyIncrementalFiberCountedClusteredBlowUpModelSubtheorems P where
  upper_geometry := h.upper_geometry
  lower_karlsson :=
    h.lower_karlsson.toFiberCountedClusteredKarlssonBlowUpIncrementalLowerData

end ConcreteFullyIncrementalCardinalityClusteredBlowUpModelSubtheorems

/-- Paper-style global geometric data whose lower construction supplies only
cluster fiber cardinalities for the finite counting part. -/
structure ManuscriptGeometricCardinalityClusteredBlowUpDataSubtheorems
    (P : TheoremOne.ProblemFamily.{u}) where
  upper_geometry : ManuscriptGeometricIncrementalUpperData P
  lower_karlsson : CardinalityClusteredKarlssonBlowUpIncrementalLowerData P

namespace ManuscriptGeometricCardinalityClusteredBlowUpDataSubtheorems

def toManuscriptGeometricFiberCountedClusteredBlowUpDataSubtheorems
    {P : TheoremOne.ProblemFamily.{u}}
    (h : ManuscriptGeometricCardinalityClusteredBlowUpDataSubtheorems P) :
    ManuscriptGeometricFiberCountedClusteredBlowUpDataSubtheorems P where
  upper_geometry := h.upper_geometry
  lower_karlsson :=
    h.lower_karlsson.toFiberCountedClusteredKarlssonBlowUpIncrementalLowerData

end ManuscriptGeometricCardinalityClusteredBlowUpDataSubtheorems

namespace ConcreteFullyIncrementalBlowUpModelSubtheorems

/-- Upgrade the older named-blow-up package to the cardinality-clustered
finite-counting package using the canonical four-fiber cluster witness. -/
noncomputable def toConcreteFullyIncrementalCardinalityClusteredBlowUpModelSubtheorems
    {P : TheoremOne.ProblemFamily.{u}}
    (h : ConcreteFullyIncrementalBlowUpModelSubtheorems P) :
    ConcreteFullyIncrementalCardinalityClusteredBlowUpModelSubtheorems P where
  upper_geometry := h.upper_geometry
  lower_karlsson :=
    h.lower_karlsson.toCardinalityClusteredKarlssonBlowUpIncrementalLowerData

end ConcreteFullyIncrementalBlowUpModelSubtheorems

namespace ManuscriptGeometricBlowUpDataSubtheorems

/-- Upgrade the older paper-style named-blow-up package to the
cardinality-clustered finite-counting package using the canonical four-fiber
cluster witness. -/
noncomputable def toManuscriptGeometricCardinalityClusteredBlowUpDataSubtheorems
    {P : TheoremOne.ProblemFamily.{u}}
    (h : ManuscriptGeometricBlowUpDataSubtheorems P) :
    ManuscriptGeometricCardinalityClusteredBlowUpDataSubtheorems P where
  upper_geometry := h.upper_geometry
  lower_karlsson :=
    h.lower_karlsson.toCardinalityClusteredKarlssonBlowUpIncrementalLowerData

end ManuscriptGeometricBlowUpDataSubtheorems

/-- Pair-counted lower obligations for a family with a named maximum count
function, in the concrete upper-data version. -/
def MaxConcreteFullyIncrementalPairCountedClusteredBlowUpModelSubtheorems
    (P : TheoremOne.MaxProblemFamily.{u}) : Type u :=
  ConcreteFullyIncrementalPairCountedClusteredBlowUpModelSubtheorems
    P.toProblemFamily

/-- Pair-counted lower obligations for a family with a named maximum count
function, in the paper-style geometric upper-data version. -/
def MaxManuscriptGeometricPairCountedClusteredBlowUpDataSubtheorems
    (P : TheoremOne.MaxProblemFamily.{u}) : Type u :=
  ManuscriptGeometricPairCountedClusteredBlowUpDataSubtheorems
    P.toProblemFamily

/-- Fiber-counted lower obligations for a family with a named maximum count
function, in the concrete upper-data version. -/
def MaxConcreteFullyIncrementalFiberCountedClusteredBlowUpModelSubtheorems
    (P : TheoremOne.MaxProblemFamily.{u}) : Type u :=
  ConcreteFullyIncrementalFiberCountedClusteredBlowUpModelSubtheorems
    P.toProblemFamily

/-- Fiber-counted lower obligations for a family with a named maximum count
function, in the paper-style geometric upper-data version. -/
def MaxManuscriptGeometricFiberCountedClusteredBlowUpDataSubtheorems
    (P : TheoremOne.MaxProblemFamily.{u}) : Type u :=
  ManuscriptGeometricFiberCountedClusteredBlowUpDataSubtheorems
    P.toProblemFamily

/-- Cardinality-only finite-counting lower obligations for a family with a
named maximum count function, in the concrete upper-data version. -/
def MaxConcreteFullyIncrementalCardinalityClusteredBlowUpModelSubtheorems
    (P : TheoremOne.MaxProblemFamily.{u}) : Type u :=
  ConcreteFullyIncrementalCardinalityClusteredBlowUpModelSubtheorems
    P.toProblemFamily

/-- Cardinality-only finite-counting lower obligations for a family with a
named maximum count function, in the paper-style geometric upper-data version. -/
def MaxManuscriptGeometricCardinalityClusteredBlowUpDataSubtheorems
    (P : TheoremOne.MaxProblemFamily.{u}) : Type u :=
  ManuscriptGeometricCardinalityClusteredBlowUpDataSubtheorems
    P.toProblemFamily

/-- Maximum-form Theorem 1 from concrete upper data and a pair-counted
clustered Karlsson blow-up lower construction. -/
theorem theorem_one_statement_proven_from_concrete_pair_counted_clustered_blowup_model
    (P : TheoremOne.ProblemFamily.{u})
    (h : ConcreteFullyIncrementalPairCountedClusteredBlowUpModelSubtheorems P) :
    TheoremOneFinal.TheoremOneStatement P := by
  exact theorem_one_statement_proven_from_concrete_clustered_blowup_model
    P h.toConcreteFullyIncrementalClusteredBlowUpModelSubtheorems

/-- Maximum-form Theorem 1 from paper-style geometric upper data and a
pair-counted clustered Karlsson blow-up lower construction. -/
theorem theorem_one_statement_proven_from_geometric_data_and_pair_counted_clustered_blowup
    (P : TheoremOne.ProblemFamily.{u})
    (h : ManuscriptGeometricPairCountedClusteredBlowUpDataSubtheorems P) :
    TheoremOneFinal.TheoremOneStatement P := by
  exact theorem_one_statement_proven_from_geometric_data_and_clustered_blowup
    P h.toManuscriptGeometricClusteredBlowUpDataSubtheorems

/-- Formula-form Theorem 1 from concrete upper data and a pair-counted
clustered Karlsson blow-up lower construction. -/
theorem theorem_one_formula_statement_proven_from_concrete_pair_counted_clustered_blowup_model
    (P : TheoremOne.MaxProblemFamily.{u})
    (h : MaxConcreteFullyIncrementalPairCountedClusteredBlowUpModelSubtheorems P) :
    TheoremOneFormulaStatement P := by
  exact theorem_one_formula_statement_proven_from_concrete_clustered_blowup_model
    P h.toConcreteFullyIncrementalClusteredBlowUpModelSubtheorems

/-- Formula-form Theorem 1 from paper-style geometric upper data and a
pair-counted clustered Karlsson blow-up lower construction. -/
theorem theorem_one_formula_statement_proven_from_geometric_data_and_pair_counted_clustered_blowup
    (P : TheoremOne.MaxProblemFamily.{u})
    (h : MaxManuscriptGeometricPairCountedClusteredBlowUpDataSubtheorems P) :
    TheoremOneFormulaStatement P := by
  exact theorem_one_formula_statement_proven_from_geometric_data_and_clustered_blowup
    P h.toManuscriptGeometricClusteredBlowUpDataSubtheorems

/-- Single-size displayed formula from concrete upper data and a pair-counted
clustered Karlsson blow-up lower construction. -/
theorem theorem_one_formula_at_proven_from_concrete_pair_counted_clustered_blowup_model
    (P : TheoremOne.MaxProblemFamily.{u})
    (h : MaxConcreteFullyIncrementalPairCountedClusteredBlowUpModelSubtheorems P)
    (n : Nat) :
    P.aLop n =
      4 * ((n.choose 2 : Nat) : Rat) + manuscriptS n + (n : Rat) + 1 := by
  exact theorem_one_formula_statement_proven_from_concrete_pair_counted_clustered_blowup_model
    P h n

/-- Single-size displayed formula from paper-style geometric upper data and a
pair-counted clustered Karlsson blow-up lower construction. -/
theorem theorem_one_formula_at_proven_from_geometric_data_and_pair_counted_clustered_blowup
    (P : TheoremOne.MaxProblemFamily.{u})
    (h : MaxManuscriptGeometricPairCountedClusteredBlowUpDataSubtheorems P)
    (n : Nat) :
    P.aLop n =
      4 * ((n.choose 2 : Nat) : Rat) + manuscriptS n + (n : Rat) + 1 := by
  exact theorem_one_formula_statement_proven_from_geometric_data_and_pair_counted_clustered_blowup
    P h n

/-- Maximum-form Theorem 1 from concrete upper data and a fiber-counted
clustered Karlsson blow-up lower construction. -/
theorem theorem_one_statement_proven_from_concrete_fiber_counted_clustered_blowup_model
    (P : TheoremOne.ProblemFamily.{u})
    (h : ConcreteFullyIncrementalFiberCountedClusteredBlowUpModelSubtheorems P) :
    TheoremOneFinal.TheoremOneStatement P := by
  exact theorem_one_statement_proven_from_concrete_pair_counted_clustered_blowup_model
    P h.toConcreteFullyIncrementalPairCountedClusteredBlowUpModelSubtheorems

/-- Maximum-form Theorem 1 from paper-style geometric upper data and a
fiber-counted clustered Karlsson blow-up lower construction. -/
theorem theorem_one_statement_proven_from_geometric_data_and_fiber_counted_clustered_blowup
    (P : TheoremOne.ProblemFamily.{u})
    (h : ManuscriptGeometricFiberCountedClusteredBlowUpDataSubtheorems P) :
    TheoremOneFinal.TheoremOneStatement P := by
  exact theorem_one_statement_proven_from_geometric_data_and_pair_counted_clustered_blowup
    P h.toManuscriptGeometricPairCountedClusteredBlowUpDataSubtheorems

/-- Formula-form Theorem 1 from concrete upper data and a fiber-counted
clustered Karlsson blow-up lower construction. -/
theorem theorem_one_formula_statement_proven_from_concrete_fiber_counted_clustered_blowup_model
    (P : TheoremOne.MaxProblemFamily.{u})
    (h : MaxConcreteFullyIncrementalFiberCountedClusteredBlowUpModelSubtheorems P) :
    TheoremOneFormulaStatement P := by
  exact theorem_one_formula_statement_proven_from_concrete_pair_counted_clustered_blowup_model
    P h.toConcreteFullyIncrementalPairCountedClusteredBlowUpModelSubtheorems

/-- Formula-form Theorem 1 from paper-style geometric upper data and a
fiber-counted clustered Karlsson blow-up lower construction. -/
theorem theorem_one_formula_statement_proven_from_geometric_data_and_fiber_counted_clustered_blowup
    (P : TheoremOne.MaxProblemFamily.{u})
    (h : MaxManuscriptGeometricFiberCountedClusteredBlowUpDataSubtheorems P) :
    TheoremOneFormulaStatement P := by
  exact theorem_one_formula_statement_proven_from_geometric_data_and_pair_counted_clustered_blowup
    P h.toManuscriptGeometricPairCountedClusteredBlowUpDataSubtheorems

/-- Single-size displayed formula from concrete upper data and a fiber-counted
clustered Karlsson blow-up lower construction. -/
theorem theorem_one_formula_at_proven_from_concrete_fiber_counted_clustered_blowup_model
    (P : TheoremOne.MaxProblemFamily.{u})
    (h : MaxConcreteFullyIncrementalFiberCountedClusteredBlowUpModelSubtheorems P)
    (n : Nat) :
    P.aLop n =
      4 * ((n.choose 2 : Nat) : Rat) + manuscriptS n + (n : Rat) + 1 := by
  exact theorem_one_formula_statement_proven_from_concrete_fiber_counted_clustered_blowup_model
    P h n

/-- Single-size displayed formula from paper-style geometric upper data and a
fiber-counted clustered Karlsson blow-up lower construction. -/
theorem theorem_one_formula_at_proven_from_geometric_data_and_fiber_counted_clustered_blowup
    (P : TheoremOne.MaxProblemFamily.{u})
    (h : MaxManuscriptGeometricFiberCountedClusteredBlowUpDataSubtheorems P)
    (n : Nat) :
    P.aLop n =
      4 * ((n.choose 2 : Nat) : Rat) + manuscriptS n + (n : Rat) + 1 := by
  exact theorem_one_formula_statement_proven_from_geometric_data_and_fiber_counted_clustered_blowup
    P h n

/-- Maximum-form Theorem 1 from concrete upper data and a cardinality-only
clustered Karlsson blow-up lower construction. -/
theorem theorem_one_statement_proven_from_concrete_cardinality_clustered_blowup_model
    (P : TheoremOne.ProblemFamily.{u})
    (h : ConcreteFullyIncrementalCardinalityClusteredBlowUpModelSubtheorems P) :
    TheoremOneFinal.TheoremOneStatement P := by
  exact theorem_one_statement_proven_from_concrete_fiber_counted_clustered_blowup_model
    P h.toConcreteFullyIncrementalFiberCountedClusteredBlowUpModelSubtheorems

/-- Maximum-form Theorem 1 from paper-style geometric upper data and a
cardinality-only clustered Karlsson blow-up lower construction. -/
theorem theorem_one_statement_proven_from_geometric_data_and_cardinality_clustered_blowup
    (P : TheoremOne.ProblemFamily.{u})
    (h : ManuscriptGeometricCardinalityClusteredBlowUpDataSubtheorems P) :
    TheoremOneFinal.TheoremOneStatement P := by
  exact theorem_one_statement_proven_from_geometric_data_and_fiber_counted_clustered_blowup
    P h.toManuscriptGeometricFiberCountedClusteredBlowUpDataSubtheorems

/-- Formula-form Theorem 1 from concrete upper data and a cardinality-only
clustered Karlsson blow-up lower construction. -/
theorem theorem_one_formula_statement_proven_from_concrete_cardinality_clustered_blowup_model
    (P : TheoremOne.MaxProblemFamily.{u})
    (h : MaxConcreteFullyIncrementalCardinalityClusteredBlowUpModelSubtheorems P) :
    TheoremOneFormulaStatement P := by
  exact theorem_one_formula_statement_proven_from_concrete_fiber_counted_clustered_blowup_model
    P h.toConcreteFullyIncrementalFiberCountedClusteredBlowUpModelSubtheorems

/-- Formula-form Theorem 1 from paper-style geometric upper data and a
cardinality-only clustered Karlsson blow-up lower construction. -/
theorem theorem_one_formula_statement_proven_from_geometric_data_and_cardinality_clustered_blowup
    (P : TheoremOne.MaxProblemFamily.{u})
    (h : MaxManuscriptGeometricCardinalityClusteredBlowUpDataSubtheorems P) :
    TheoremOneFormulaStatement P := by
  exact theorem_one_formula_statement_proven_from_geometric_data_and_fiber_counted_clustered_blowup
    P h.toManuscriptGeometricFiberCountedClusteredBlowUpDataSubtheorems

/-- Single-size displayed formula from concrete upper data and a
cardinality-only clustered Karlsson blow-up lower construction. -/
theorem theorem_one_formula_at_proven_from_concrete_cardinality_clustered_blowup_model
    (P : TheoremOne.MaxProblemFamily.{u})
    (h : MaxConcreteFullyIncrementalCardinalityClusteredBlowUpModelSubtheorems P)
    (n : Nat) :
    P.aLop n =
      4 * ((n.choose 2 : Nat) : Rat) + manuscriptS n + (n : Rat) + 1 := by
  exact theorem_one_formula_statement_proven_from_concrete_cardinality_clustered_blowup_model
    P h n

/-- Single-size displayed formula from paper-style geometric upper data and a
cardinality-only clustered Karlsson blow-up lower construction. -/
theorem theorem_one_formula_at_proven_from_geometric_data_and_cardinality_clustered_blowup
    (P : TheoremOne.MaxProblemFamily.{u})
    (h : MaxManuscriptGeometricCardinalityClusteredBlowUpDataSubtheorems P)
    (n : Nat) :
    P.aLop n =
      4 * ((n.choose 2 : Nat) : Rat) + manuscriptS n + (n : Rat) + 1 := by
  exact theorem_one_formula_statement_proven_from_geometric_data_and_cardinality_clustered_blowup
    P h n

end ExplicitInputs
end TheoremOneManuscript
end Lollipop
