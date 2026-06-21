import Lollipop.Internal.Manuscript.FormalizedProof.FinalTheorem

/-!
Manuscript proof dependency graph.

This module is intentionally small and non-disruptive.  It states the
paper-scale inputs that are still model-specific certificates, then proves the
displayed Theorem 1 statement from them.  All generic lemmas in the route
through the region equation, close/intriguing reduction, colored Zykov,
weighted Turan, partition matrix bookkeeping, Section 5, sorted `S(n)`, and
Karlsson finite counting are imported as proved Lean theorems.
-/

namespace Lollipop
namespace TheoremOneManuscript
namespace FormalizedProof

universe u

/-- The remaining model-specific certificate producers for the current
manuscript endpoint.

The upper field supplies primitive carrier component-savings certificates for
the geometric close/intriguing pair bounds.  The lower field supplies
Karlsson's four-base table together with local blow-up and ordered-insertion
data.  Lean proves the generic theorem-one chain from these fields. -/
structure TheoremOneDependencyGraph
    (P : TheoremOne.MaxProblemFamily.{u}) : Type u where
  upper_geometry :
    PrimitiveGeometry.PrimitiveCarrierComponentSavingsUpperGeometryData
      P.toProblemFamily
  lower_karlsson_base :
    ExplicitInputs.KarlssonBaseBlowUpIncrementalLowerData P.toProblemFamily

/-- Direct whole-carrier savings dependency graph.  This is the preferred
boundary for completing the close/intriguing route-savings proof when the
argument is coupled across carrier components. -/
structure DirectSavingsTheoremOneDependencyGraph
    (P : TheoremOne.MaxProblemFamily.{u}) : Type u where
  upper_geometry :
    PrimitiveGeometry.PrimitiveCarrierDirectSavingsUpperGeometryData
      P.toProblemFamily
  lower_karlsson_base :
    ExplicitInputs.KarlssonBaseBlowUpIncrementalLowerData P.toProblemFamily

/-- Radial-outward version of the dependency graph.  This is the manuscript
faithful upper boundary: every primitive lollipop stem is recorded as radial
outward, and the component-savings/crossing certificates are the same as in
`TheoremOneDependencyGraph`. -/
structure RadialTheoremOneDependencyGraph
    (P : TheoremOne.MaxProblemFamily.{u}) : Type u where
  upper_geometry :
    PrimitiveGeometry.PrimitiveRadialCarrierComponentSavingsUpperGeometryData
      P.toProblemFamily
  lower_karlsson_base :
    ExplicitInputs.KarlssonBaseBlowUpIncrementalLowerData P.toProblemFamily

/-- Radial-outward version of the direct whole-carrier savings dependency
graph. -/
structure DirectSavingsRadialTheoremOneDependencyGraph
    (P : TheoremOne.MaxProblemFamily.{u}) : Type u where
  upper_geometry :
    PrimitiveGeometry.PrimitiveRadialCarrierDirectSavingsUpperGeometryData
      P.toProblemFamily
  lower_karlsson_base :
    ExplicitInputs.KarlssonBaseBlowUpIncrementalLowerData P.toProblemFamily

/-- Routed version of the dependency graph: the upper close/intriguing
component savings are supplied through named geometric route constructors,
then Lean converts those routes into the component-savings package. -/
structure RoutedTheoremOneDependencyGraph
    (P : TheoremOne.MaxProblemFamily.{u}) : Type u where
  upper_geometry :
    PrimitiveGeometry.PrimitiveCarrierRoutedComponentSavingsUpperGeometryData
      P.toProblemFamily
  lower_karlsson_base :
    ExplicitInputs.KarlssonBaseBlowUpIncrementalLowerData P.toProblemFamily

/-- Radial-outward routed dependency graph, matching the manuscript stem
condition while keeping the close/intriguing savings route-based. -/
structure RoutedRadialTheoremOneDependencyGraph
    (P : TheoremOne.MaxProblemFamily.{u}) : Type u where
  upper_geometry :
    PrimitiveGeometry.PrimitiveRadialCarrierRoutedComponentSavingsUpperGeometryData
      P.toProblemFamily
  lower_karlsson_base :
    ExplicitInputs.KarlssonBaseBlowUpIncrementalLowerData P.toProblemFamily

namespace TheoremOneDependencyGraph

/-- Convert the explicit proof-DAG fields to the theorem package used by the
formalized manuscript proof. -/
noncomputable def toKarlssonBaseLowerSubtheorems
    {P : TheoremOne.MaxProblemFamily.{u}}
    (h : TheoremOneDependencyGraph P) :
    KarlssonBaseLowerTheoremOneSubtheorems P where
  upper_geometry := h.upper_geometry
  lower_karlsson_base := h.lower_karlsson_base

end TheoremOneDependencyGraph

namespace DirectSavingsTheoremOneDependencyGraph

/-- Convert direct whole-carrier proof-DAG fields to the theorem package used
by the formalized manuscript proof. -/
noncomputable def toDirectSavingsKarlssonBaseLowerSubtheorems
    {P : TheoremOne.MaxProblemFamily.{u}}
    (h : DirectSavingsTheoremOneDependencyGraph P) :
    DirectSavingsKarlssonBaseLowerTheoremOneSubtheorems P where
  upper_geometry := h.upper_geometry
  lower_karlsson_base := h.lower_karlsson_base

end DirectSavingsTheoremOneDependencyGraph

namespace RadialTheoremOneDependencyGraph

/-- Forget only the radial-outward record, after it has been made explicit at
the manuscript-facing proof boundary. -/
noncomputable def toTheoremOneDependencyGraph
    {P : TheoremOne.MaxProblemFamily.{u}}
    (h : RadialTheoremOneDependencyGraph P) :
    TheoremOneDependencyGraph P where
  upper_geometry := h.upper_geometry.toComponentSavingsUpperGeometryData
  lower_karlsson_base := h.lower_karlsson_base

end RadialTheoremOneDependencyGraph

namespace DirectSavingsRadialTheoremOneDependencyGraph

/-- Forget only the radial-outward record in the direct-savings graph. -/
noncomputable def toDirectSavingsTheoremOneDependencyGraph
    {P : TheoremOne.MaxProblemFamily.{u}}
    (h : DirectSavingsRadialTheoremOneDependencyGraph P) :
    DirectSavingsTheoremOneDependencyGraph P where
  upper_geometry := h.upper_geometry.toDirectSavingsUpperGeometryData
  lower_karlsson_base := h.lower_karlsson_base

end DirectSavingsRadialTheoremOneDependencyGraph

namespace RoutedTheoremOneDependencyGraph

/-- Convert the routed proof-DAG fields to the existing dependency graph by
converting named route certificates into component-savings certificates. -/
noncomputable def toTheoremOneDependencyGraph
    {P : TheoremOne.MaxProblemFamily.{u}}
    (h : RoutedTheoremOneDependencyGraph P) :
    TheoremOneDependencyGraph P where
  upper_geometry := h.upper_geometry.toComponentSavingsUpperGeometryData
  lower_karlsson_base := h.lower_karlsson_base

end RoutedTheoremOneDependencyGraph

namespace RoutedRadialTheoremOneDependencyGraph

/-- Convert routed radial proof-DAG fields to the radial dependency graph by
converting named route certificates into component-savings certificates. -/
noncomputable def toRadialTheoremOneDependencyGraph
    {P : TheoremOne.MaxProblemFamily.{u}}
    (h : RoutedRadialTheoremOneDependencyGraph P) :
    RadialTheoremOneDependencyGraph P where
  upper_geometry := h.upper_geometry.toRadialComponentSavingsUpperGeometryData
  lower_karlsson_base := h.lower_karlsson_base

/-- Forget the radial field after converting route certificates to
component-savings certificates. -/
noncomputable def toTheoremOneDependencyGraph
    {P : TheoremOne.MaxProblemFamily.{u}}
    (h : RoutedRadialTheoremOneDependencyGraph P) :
    TheoremOneDependencyGraph P :=
  h.toRadialTheoremOneDependencyGraph.toTheoremOneDependencyGraph

end RoutedRadialTheoremOneDependencyGraph

/-- The displayed manuscript Theorem 1 formula follows from the explicit
proof-DAG certificate producers. -/
theorem theorem_one_from_dependency_graph
    (P : TheoremOne.MaxProblemFamily.{u})
    (h : TheoremOneDependencyGraph P) :
    FinalTheoremOneStatement P := by
  exact theorem_one_from_karlsson_base_lower_subtheorems P
    h.toKarlssonBaseLowerSubtheorems

/-- Single-size displayed formula from the explicit proof-DAG certificate
producers. -/
theorem theorem_one_at_from_dependency_graph
    (P : TheoremOne.MaxProblemFamily.{u})
    (h : TheoremOneDependencyGraph P)
    (n : Nat) :
    FinalTheoremOneAtStatement P n := by
  exact theorem_one_from_dependency_graph P h n

/-- The displayed manuscript Theorem 1 formula follows from the direct
whole-carrier savings proof-DAG certificate producers. -/
theorem theorem_one_from_direct_savings_dependency_graph
    (P : TheoremOne.MaxProblemFamily.{u})
    (h : DirectSavingsTheoremOneDependencyGraph P) :
    FinalTheoremOneStatement P := by
  exact theorem_one_from_direct_savings_karlsson_base_lower_subtheorems P
    h.toDirectSavingsKarlssonBaseLowerSubtheorems

/-- Single-size displayed formula from the direct whole-carrier savings
proof-DAG certificate producers. -/
theorem theorem_one_at_from_direct_savings_dependency_graph
    (P : TheoremOne.MaxProblemFamily.{u})
    (h : DirectSavingsTheoremOneDependencyGraph P)
    (n : Nat) :
    FinalTheoremOneAtStatement P n := by
  exact theorem_one_from_direct_savings_dependency_graph P h n

/-- The displayed manuscript Theorem 1 formula follows from the radial-outward
proof-DAG certificate producers. -/
theorem theorem_one_from_radial_dependency_graph
    (P : TheoremOne.MaxProblemFamily.{u})
    (h : RadialTheoremOneDependencyGraph P) :
    FinalTheoremOneStatement P := by
  exact theorem_one_from_dependency_graph P h.toTheoremOneDependencyGraph

/-- Single-size displayed formula from the radial-outward proof-DAG
certificate producers. -/
theorem theorem_one_at_from_radial_dependency_graph
    (P : TheoremOne.MaxProblemFamily.{u})
    (h : RadialTheoremOneDependencyGraph P)
    (n : Nat) :
    FinalTheoremOneAtStatement P n := by
  exact theorem_one_from_radial_dependency_graph P h n

/-- The displayed manuscript Theorem 1 formula follows from the radial
direct-savings proof-DAG certificate producers. -/
theorem theorem_one_from_direct_savings_radial_dependency_graph
    (P : TheoremOne.MaxProblemFamily.{u})
    (h : DirectSavingsRadialTheoremOneDependencyGraph P) :
    FinalTheoremOneStatement P := by
  exact theorem_one_from_direct_savings_dependency_graph P
    h.toDirectSavingsTheoremOneDependencyGraph

/-- Single-size displayed formula from the radial direct-savings proof-DAG
certificate producers. -/
theorem theorem_one_at_from_direct_savings_radial_dependency_graph
    (P : TheoremOne.MaxProblemFamily.{u})
    (h : DirectSavingsRadialTheoremOneDependencyGraph P)
    (n : Nat) :
    FinalTheoremOneAtStatement P n := by
  exact theorem_one_from_direct_savings_radial_dependency_graph P h n

/-- The displayed manuscript Theorem 1 formula follows from routed proof-DAG
certificate producers. -/
theorem theorem_one_from_routed_dependency_graph
    (P : TheoremOne.MaxProblemFamily.{u})
    (h : RoutedTheoremOneDependencyGraph P) :
    FinalTheoremOneStatement P := by
  exact theorem_one_from_dependency_graph P h.toTheoremOneDependencyGraph

/-- Single-size displayed formula from routed proof-DAG certificate
producers. -/
theorem theorem_one_at_from_routed_dependency_graph
    (P : TheoremOne.MaxProblemFamily.{u})
    (h : RoutedTheoremOneDependencyGraph P)
    (n : Nat) :
    FinalTheoremOneAtStatement P n := by
  exact theorem_one_from_routed_dependency_graph P h n

/-- The displayed manuscript Theorem 1 formula follows from routed radial
proof-DAG certificate producers. -/
theorem theorem_one_from_routed_radial_dependency_graph
    (P : TheoremOne.MaxProblemFamily.{u})
    (h : RoutedRadialTheoremOneDependencyGraph P) :
    FinalTheoremOneStatement P := by
  exact theorem_one_from_radial_dependency_graph P
    h.toRadialTheoremOneDependencyGraph

/-- Single-size displayed formula from routed radial proof-DAG certificate
producers. -/
theorem theorem_one_at_from_routed_radial_dependency_graph
    (P : TheoremOne.MaxProblemFamily.{u})
    (h : RoutedRadialTheoremOneDependencyGraph P)
    (n : Nat) :
    FinalTheoremOneAtStatement P n := by
  exact theorem_one_from_routed_radial_dependency_graph P h n

end FormalizedProof
end TheoremOneManuscript
end Lollipop
