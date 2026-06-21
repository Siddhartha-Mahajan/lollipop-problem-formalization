import Lollipop.Internal.Manuscript.Formalization.FromSubtheorems
import Lollipop.Internal.Manuscript.ExplicitInputs.KarlssonBase
import Lollipop.Internal.Manuscript.ExplicitInputs.PairwiseLower
import Lollipop.Internal.Manuscript.PrimitiveGeometry.CarrierSavings
import Lollipop.Internal.Manuscript.PrimitiveGeometry.ComponentBounds

/-!
Theorem 1 from primitive carrier component bounds.

This theorem-facing file is one step closer to the manuscript's geometric
Lemma 2 than `FromSubtheorems`: the baseline `≤ 7` pair-crossing
case is not assumed as a table entry.  It is proved from finite
carrier-intersection witnesses plus the generic noncoincidence of the two
circles and two ray-supporting lines.  The strongest endpoint in this file
also makes the close/intriguing `≤ 5/4` savings component-wise finite
cardinality obligations rather than final numeric crossing inequalities.
-/

namespace Lollipop
namespace TheoremOneManuscript

universe u

/-- Component-bound primitive carrier subtheorems for Theorem 1: the upper
side derives the generic `≤ 7` crossing case from carrier components, and the
lower side is the named incremental Karlsson blow-up construction. -/
structure ComponentBoundPrimitiveCarrierTheoremOneSubtheorems
    (P : TheoremOne.MaxProblemFamily.{u}) where
  upper_geometry :
    PrimitiveGeometry.PrimitiveCarrierComponentBoundUpperGeometryData
      P.toProblemFamily
  lower_karlsson :
    ExplicitInputs.KarlssonBlowUpIncrementalLowerData P.toProblemFamily

namespace ComponentBoundPrimitiveCarrierTheoremOneSubtheorems

/-- Forget the proof of the generic `≤ 7` case after converting it to the
existing primitive carrier-certified theorem-one package. -/
noncomputable def toPrimitiveCarrierTheoremOneSubtheorems
    {P : TheoremOne.MaxProblemFamily.{u}}
    (h : ComponentBoundPrimitiveCarrierTheoremOneSubtheorems P) :
    PrimitiveCarrierTheoremOneSubtheorems P where
  upper_geometry :=
    h.upper_geometry.toPrimitiveCarrierCertifiedExactUpperGeometryData
  lower_karlsson := h.lower_karlsson

end ComponentBoundPrimitiveCarrierTheoremOneSubtheorems

/-- Theorem 1 from primitive carrier component bounds and named Karlsson
blow-up data. -/
theorem theorem_one_from_component_bound_primitive_carrier_subtheorems
    (P : TheoremOne.MaxProblemFamily.{u})
    (h : ComponentBoundPrimitiveCarrierTheoremOneSubtheorems P) :
    TheoremOneStatement P := by
  exact theorem_one_from_primitive_carrier_subtheorems P
    h.toPrimitiveCarrierTheoremOneSubtheorems

/-- Single-size Theorem 1 formula from primitive carrier component bounds and
named Karlsson blow-up data. -/
theorem theorem_one_at_from_component_bound_primitive_carrier_subtheorems
    (P : TheoremOne.MaxProblemFamily.{u})
    (h : ComponentBoundPrimitiveCarrierTheoremOneSubtheorems P)
    (n : Nat) :
    P.aLop n =
      4 * ((n.choose 2 : Nat) : Rat) + manuscriptS n + (n : Rat) + 1 := by
  exact theorem_one_from_component_bound_primitive_carrier_subtheorems P h n

/-- Component-savings primitive carrier subtheorems for Theorem 1: the upper
side derives the generic `≤ 7` case and derives the close/intriguing `≤ 5/4`
cases from component-wise finite-cardinality savings. -/
structure ComponentSavingsPrimitiveCarrierTheoremOneSubtheorems
    (P : TheoremOne.MaxProblemFamily.{u}) where
  upper_geometry :
    PrimitiveGeometry.PrimitiveCarrierComponentSavingsUpperGeometryData
      P.toProblemFamily
  lower_karlsson :
    ExplicitInputs.KarlssonBlowUpIncrementalLowerData P.toProblemFamily

namespace ComponentSavingsPrimitiveCarrierTheoremOneSubtheorems

/-- Forget the component-wise proof details after converting them to the
existing primitive carrier-certified theorem-one package. -/
noncomputable def toPrimitiveCarrierTheoremOneSubtheorems
    {P : TheoremOne.MaxProblemFamily.{u}}
    (h : ComponentSavingsPrimitiveCarrierTheoremOneSubtheorems P) :
    PrimitiveCarrierTheoremOneSubtheorems P where
  upper_geometry :=
    h.upper_geometry.toPrimitiveCarrierCertifiedExactUpperGeometryData
  lower_karlsson := h.lower_karlsson

end ComponentSavingsPrimitiveCarrierTheoremOneSubtheorems

/-- Theorem 1 from primitive carrier component savings and named Karlsson
blow-up data. -/
theorem theorem_one_from_component_savings_primitive_carrier_subtheorems
    (P : TheoremOne.MaxProblemFamily.{u})
    (h : ComponentSavingsPrimitiveCarrierTheoremOneSubtheorems P) :
    TheoremOneStatement P := by
  exact theorem_one_from_primitive_carrier_subtheorems P
    h.toPrimitiveCarrierTheoremOneSubtheorems

/-- Single-size Theorem 1 formula from primitive carrier component savings
and named Karlsson blow-up data. -/
theorem theorem_one_at_from_component_savings_primitive_carrier_subtheorems
    (P : TheoremOne.MaxProblemFamily.{u})
    (h : ComponentSavingsPrimitiveCarrierTheoremOneSubtheorems P)
    (n : Nat) :
    P.aLop n =
      4 * ((n.choose 2 : Nat) : Rat) + manuscriptS n + (n : Rat) + 1 := by
  exact theorem_one_from_component_savings_primitive_carrier_subtheorems P h n

/-- Direct-savings primitive carrier subtheorems for Theorem 1: the upper
side derives the generic `≤ 7` case and derives the close/intriguing `≤ 5/4`
cases from whole-carrier finite-cardinality savings. -/
structure DirectSavingsPrimitiveCarrierTheoremOneSubtheorems
    (P : TheoremOne.MaxProblemFamily.{u}) where
  upper_geometry :
    PrimitiveGeometry.PrimitiveCarrierDirectSavingsUpperGeometryData
      P.toProblemFamily
  lower_karlsson :
    ExplicitInputs.KarlssonBlowUpIncrementalLowerData P.toProblemFamily

namespace DirectSavingsPrimitiveCarrierTheoremOneSubtheorems

/-- Forget direct whole-carrier proof details after converting them to the
existing primitive carrier-certified theorem-one package. -/
noncomputable def toPrimitiveCarrierTheoremOneSubtheorems
    {P : TheoremOne.MaxProblemFamily.{u}}
    (h : DirectSavingsPrimitiveCarrierTheoremOneSubtheorems P) :
    PrimitiveCarrierTheoremOneSubtheorems P where
  upper_geometry :=
    h.upper_geometry.toPrimitiveCarrierCertifiedExactUpperGeometryData
  lower_karlsson := h.lower_karlsson

end DirectSavingsPrimitiveCarrierTheoremOneSubtheorems

/-- Theorem 1 from primitive carrier direct savings and named Karlsson
blow-up data. -/
theorem theorem_one_from_direct_savings_primitive_carrier_subtheorems
    (P : TheoremOne.MaxProblemFamily.{u})
    (h : DirectSavingsPrimitiveCarrierTheoremOneSubtheorems P) :
    TheoremOneStatement P := by
  exact theorem_one_from_primitive_carrier_subtheorems P
    h.toPrimitiveCarrierTheoremOneSubtheorems

/-- Single-size formula from primitive carrier direct savings and named
Karlsson blow-up data. -/
theorem theorem_one_at_from_direct_savings_primitive_carrier_subtheorems
    (P : TheoremOne.MaxProblemFamily.{u})
    (h : DirectSavingsPrimitiveCarrierTheoremOneSubtheorems P)
    (n : Nat) :
    P.aLop n =
      4 * ((n.choose 2 : Nat) : Rat) + manuscriptS n + (n : Rat) + 1 := by
  exact theorem_one_from_direct_savings_primitive_carrier_subtheorems P h n

/-- Stronger lower-bound endpoint: the lower construction supplies pairwise
crossing values and ordered insertion-region data.  Lean sums those pairwise
values to the Karlsson lower polynomial before invoking the theorem stack. -/
structure ComponentSavingsPairwiseLowerPrimitiveCarrierTheoremOneSubtheorems
    (P : TheoremOne.MaxProblemFamily.{u}) where
  upper_geometry :
    PrimitiveGeometry.PrimitiveCarrierComponentSavingsUpperGeometryData
      P.toProblemFamily
  lower_pairwise :
    ExplicitInputs.PairwiseCardinalityClusteredKarlssonBlowUpIncrementalLowerData
      P.toProblemFamily

namespace ComponentSavingsPairwiseLowerPrimitiveCarrierTheoremOneSubtheorems

/-- Convert the pairwise lower package to the older component-savings theorem
package after Lean has derived the aggregate Karlsson lower data. -/
noncomputable def toComponentSavingsPrimitiveCarrierTheoremOneSubtheorems
    {P : TheoremOne.MaxProblemFamily.{u}}
    (h : ComponentSavingsPairwiseLowerPrimitiveCarrierTheoremOneSubtheorems P) :
    ComponentSavingsPrimitiveCarrierTheoremOneSubtheorems P where
  upper_geometry := h.upper_geometry
  lower_karlsson := h.lower_pairwise.toKarlssonBlowUpIncrementalLowerData

end ComponentSavingsPairwiseLowerPrimitiveCarrierTheoremOneSubtheorems

/-- Theorem 1 from primitive carrier component savings and pairwise Karlsson
lower construction data. -/
theorem theorem_one_from_component_savings_pairwise_lower_primitive_carrier_subtheorems
    (P : TheoremOne.MaxProblemFamily.{u})
    (h : ComponentSavingsPairwiseLowerPrimitiveCarrierTheoremOneSubtheorems P) :
    TheoremOneStatement P := by
  exact theorem_one_from_component_savings_primitive_carrier_subtheorems P
    h.toComponentSavingsPrimitiveCarrierTheoremOneSubtheorems

/-- Single-size formula from primitive carrier component savings and pairwise
Karlsson lower construction data. -/
theorem theorem_one_at_from_component_savings_pairwise_lower_primitive_carrier_subtheorems
    (P : TheoremOne.MaxProblemFamily.{u})
    (h : ComponentSavingsPairwiseLowerPrimitiveCarrierTheoremOneSubtheorems P)
    (n : Nat) :
    P.aLop n =
      4 * ((n.choose 2 : Nat) : Rat) + manuscriptS n + (n : Rat) + 1 := by
  exact
    theorem_one_from_component_savings_pairwise_lower_primitive_carrier_subtheorems
      P h n

/-- Direct-savings endpoint with pairwise Karlsson lower construction data. -/
structure DirectSavingsPairwiseLowerPrimitiveCarrierTheoremOneSubtheorems
    (P : TheoremOne.MaxProblemFamily.{u}) where
  upper_geometry :
    PrimitiveGeometry.PrimitiveCarrierDirectSavingsUpperGeometryData
      P.toProblemFamily
  lower_pairwise :
    ExplicitInputs.PairwiseCardinalityClusteredKarlssonBlowUpIncrementalLowerData
      P.toProblemFamily

namespace DirectSavingsPairwiseLowerPrimitiveCarrierTheoremOneSubtheorems

/-- Convert the pairwise lower package to the older direct-savings theorem
package after Lean has derived the aggregate Karlsson lower data. -/
noncomputable def toDirectSavingsPrimitiveCarrierTheoremOneSubtheorems
    {P : TheoremOne.MaxProblemFamily.{u}}
    (h : DirectSavingsPairwiseLowerPrimitiveCarrierTheoremOneSubtheorems P) :
    DirectSavingsPrimitiveCarrierTheoremOneSubtheorems P where
  upper_geometry := h.upper_geometry
  lower_karlsson := h.lower_pairwise.toKarlssonBlowUpIncrementalLowerData

end DirectSavingsPairwiseLowerPrimitiveCarrierTheoremOneSubtheorems

/-- Theorem 1 from primitive carrier direct savings and pairwise Karlsson
lower construction data. -/
theorem theorem_one_from_direct_savings_pairwise_lower_primitive_carrier_subtheorems
    (P : TheoremOne.MaxProblemFamily.{u})
    (h : DirectSavingsPairwiseLowerPrimitiveCarrierTheoremOneSubtheorems P) :
    TheoremOneStatement P := by
  exact theorem_one_from_direct_savings_primitive_carrier_subtheorems P
    h.toDirectSavingsPrimitiveCarrierTheoremOneSubtheorems

/-- Single-size formula from primitive carrier direct savings and pairwise
Karlsson lower construction data. -/
theorem theorem_one_at_from_direct_savings_pairwise_lower_primitive_carrier_subtheorems
    (P : TheoremOne.MaxProblemFamily.{u})
    (h : DirectSavingsPairwiseLowerPrimitiveCarrierTheoremOneSubtheorems P)
    (n : Nat) :
    P.aLop n =
      4 * ((n.choose 2 : Nat) : Rat) + manuscriptS n + (n : Rat) + 1 := by
  exact
    theorem_one_from_direct_savings_pairwise_lower_primitive_carrier_subtheorems
      P h n

/-- Monotone lower-bound endpoint: the upper side is component-savings
primitive carrier geometry, while the lower construction only proves each
copy pair has at least the corresponding Karlsson cluster-table value. -/
structure ComponentSavingsMonotonePairwiseLowerPrimitiveCarrierTheoremOneSubtheorems
    (P : TheoremOne.MaxProblemFamily.{u}) where
  upper_geometry :
    PrimitiveGeometry.PrimitiveCarrierComponentSavingsUpperGeometryData
      P.toProblemFamily
  lower_pairwise_bound :
    ExplicitInputs.PairwiseCardinalityClusteredKarlssonBlowUpIncrementalLowerBoundData
      P.toProblemFamily

namespace ComponentSavingsMonotonePairwiseLowerPrimitiveCarrierTheoremOneSubtheorems

/-- Convert component-savings upper data plus monotone pairwise lower data to
the statement-layer monotone theorem package. -/
noncomputable def toMaxCanonicalExactCoordinateGeometricCrossingModelBoundSubtheorems
    {P : TheoremOne.MaxProblemFamily.{u}}
    (h :
      ComponentSavingsMonotonePairwiseLowerPrimitiveCarrierTheoremOneSubtheorems
        P) :
    MaxCanonicalExactCoordinateGeometricCrossingModelBoundSubtheorems P where
  upper_certificates :=
    h.upper_geometry
      |>.toPrimitiveCarrierCertifiedExactUpperGeometryData
      |>.toCanonicalExactUpperGeometryIncrementalData
      |>.toUpperCertificates
  lower_sorted_crossing_bound_realizations :=
    ⟨h.lower_pairwise_bound.crossings,
      h.lower_pairwise_bound.toSortedLowerCrossingBoundRealizations⟩

end ComponentSavingsMonotonePairwiseLowerPrimitiveCarrierTheoremOneSubtheorems

/-- Theorem 1 from component-savings primitive carrier upper data and
monotone pairwise Karlsson lower data. -/
theorem theorem_one_from_component_savings_monotone_pairwise_lower_primitive_carrier_subtheorems
    (P : TheoremOne.MaxProblemFamily.{u})
    (h : ComponentSavingsMonotonePairwiseLowerPrimitiveCarrierTheoremOneSubtheorems
      P) :
    TheoremOneStatement P := by
  exact
    theorem_one_formula_statement_proven_from_manuscript_canonical_exact_coordinate_geometric_crossing_bound_certificates
      P h.toMaxCanonicalExactCoordinateGeometricCrossingModelBoundSubtheorems

/-- Single-size formula from component-savings primitive carrier upper data
and monotone pairwise Karlsson lower data. -/
theorem theorem_one_at_from_component_savings_monotone_pairwise_lower_primitive_carrier_subtheorems
    (P : TheoremOne.MaxProblemFamily.{u})
    (h : ComponentSavingsMonotonePairwiseLowerPrimitiveCarrierTheoremOneSubtheorems
      P)
    (n : Nat) :
    P.aLop n =
      4 * ((n.choose 2 : Nat) : Rat) + manuscriptS n + (n : Rat) + 1 := by
  exact
    theorem_one_from_component_savings_monotone_pairwise_lower_primitive_carrier_subtheorems
      P h n

/-- Direct-savings version of the monotone pairwise lower endpoint. -/
structure DirectSavingsMonotonePairwiseLowerPrimitiveCarrierTheoremOneSubtheorems
    (P : TheoremOne.MaxProblemFamily.{u}) where
  upper_geometry :
    PrimitiveGeometry.PrimitiveCarrierDirectSavingsUpperGeometryData
      P.toProblemFamily
  lower_pairwise_bound :
    ExplicitInputs.PairwiseCardinalityClusteredKarlssonBlowUpIncrementalLowerBoundData
      P.toProblemFamily

namespace DirectSavingsMonotonePairwiseLowerPrimitiveCarrierTheoremOneSubtheorems

/-- Convert direct whole-carrier upper data plus monotone pairwise lower data
to the statement-layer monotone theorem package. -/
noncomputable def toMaxCanonicalExactCoordinateGeometricCrossingModelBoundSubtheorems
    {P : TheoremOne.MaxProblemFamily.{u}}
    (h :
      DirectSavingsMonotonePairwiseLowerPrimitiveCarrierTheoremOneSubtheorems
        P) :
    MaxCanonicalExactCoordinateGeometricCrossingModelBoundSubtheorems P where
  upper_certificates :=
    h.upper_geometry
      |>.toPrimitiveCarrierCertifiedExactUpperGeometryData
      |>.toCanonicalExactUpperGeometryIncrementalData
      |>.toUpperCertificates
  lower_sorted_crossing_bound_realizations :=
    ⟨h.lower_pairwise_bound.crossings,
      h.lower_pairwise_bound.toSortedLowerCrossingBoundRealizations⟩

end DirectSavingsMonotonePairwiseLowerPrimitiveCarrierTheoremOneSubtheorems

/-- Theorem 1 from direct whole-carrier primitive upper data and monotone
pairwise Karlsson lower data. -/
theorem theorem_one_from_direct_savings_monotone_pairwise_lower_primitive_carrier_subtheorems
    (P : TheoremOne.MaxProblemFamily.{u})
    (h :
      DirectSavingsMonotonePairwiseLowerPrimitiveCarrierTheoremOneSubtheorems
        P) :
    TheoremOneStatement P := by
  exact
    theorem_one_formula_statement_proven_from_manuscript_canonical_exact_coordinate_geometric_crossing_bound_certificates
      P h.toMaxCanonicalExactCoordinateGeometricCrossingModelBoundSubtheorems

/-- Single-size formula from direct whole-carrier primitive upper data and
monotone pairwise Karlsson lower data. -/
theorem theorem_one_at_from_direct_savings_monotone_pairwise_lower_primitive_carrier_subtheorems
    (P : TheoremOne.MaxProblemFamily.{u})
    (h :
      DirectSavingsMonotonePairwiseLowerPrimitiveCarrierTheoremOneSubtheorems
        P)
    (n : Nat) :
    P.aLop n =
      4 * ((n.choose 2 : Nat) : Rat) + manuscriptS n + (n : Rat) + 1 := by
  exact
    theorem_one_from_direct_savings_monotone_pairwise_lower_primitive_carrier_subtheorems
      P h n

/-- Strongest lower-bound endpoint in this file: the lower construction names
Karlsson's four-base table and supplies local blow-up/insertion certificates.
Lean converts that data to the pairwise lower interface, then sums the
pairwise table to the lower polynomial. -/
structure ComponentSavingsKarlssonBaseLowerPrimitiveCarrierTheoremOneSubtheorems
    (P : TheoremOne.MaxProblemFamily.{u}) where
  upper_geometry :
    PrimitiveGeometry.PrimitiveCarrierComponentSavingsUpperGeometryData
      P.toProblemFamily
  lower_karlsson_base :
    ExplicitInputs.KarlssonBaseBlowUpIncrementalLowerData P.toProblemFamily

namespace ComponentSavingsKarlssonBaseLowerPrimitiveCarrierTheoremOneSubtheorems

/-- Convert the four-base/local-blow-up lower package to the pairwise lower
theorem package. -/
noncomputable def toComponentSavingsPairwiseLowerPrimitiveCarrierTheoremOneSubtheorems
    {P : TheoremOne.MaxProblemFamily.{u}}
    (h : ComponentSavingsKarlssonBaseLowerPrimitiveCarrierTheoremOneSubtheorems P) :
    ComponentSavingsPairwiseLowerPrimitiveCarrierTheoremOneSubtheorems P where
  upper_geometry := h.upper_geometry
  lower_pairwise :=
    h.lower_karlsson_base
      |>.toPairwiseCardinalityClusteredKarlssonBlowUpIncrementalLowerData

end ComponentSavingsKarlssonBaseLowerPrimitiveCarrierTheoremOneSubtheorems

/-- Theorem 1 from primitive carrier component savings plus Karlsson
four-base/local-blow-up lower construction data. -/
theorem theorem_one_from_component_savings_karlsson_base_lower_primitive_carrier_subtheorems
    (P : TheoremOne.MaxProblemFamily.{u})
    (h : ComponentSavingsKarlssonBaseLowerPrimitiveCarrierTheoremOneSubtheorems P) :
    TheoremOneStatement P := by
  exact theorem_one_from_component_savings_pairwise_lower_primitive_carrier_subtheorems
    P h.toComponentSavingsPairwiseLowerPrimitiveCarrierTheoremOneSubtheorems

/-- Single-size formula from primitive carrier component savings plus
Karlsson four-base/local-blow-up lower construction data. -/
theorem theorem_one_at_from_component_savings_karlsson_base_lower_primitive_carrier_subtheorems
    (P : TheoremOne.MaxProblemFamily.{u})
    (h : ComponentSavingsKarlssonBaseLowerPrimitiveCarrierTheoremOneSubtheorems P)
    (n : Nat) :
    P.aLop n =
      4 * ((n.choose 2 : Nat) : Rat) + manuscriptS n + (n : Rat) + 1 := by
  exact
    theorem_one_from_component_savings_karlsson_base_lower_primitive_carrier_subtheorems
      P h n

/-- Direct-savings endpoint with Karlsson four-base/local-blow-up lower
construction data. -/
structure DirectSavingsKarlssonBaseLowerPrimitiveCarrierTheoremOneSubtheorems
    (P : TheoremOne.MaxProblemFamily.{u}) where
  upper_geometry :
    PrimitiveGeometry.PrimitiveCarrierDirectSavingsUpperGeometryData
      P.toProblemFamily
  lower_karlsson_base :
    ExplicitInputs.KarlssonBaseBlowUpIncrementalLowerData P.toProblemFamily

namespace DirectSavingsKarlssonBaseLowerPrimitiveCarrierTheoremOneSubtheorems

/-- Convert the four-base/local-blow-up lower package to the pairwise lower
direct-savings theorem package. -/
noncomputable def toDirectSavingsPairwiseLowerPrimitiveCarrierTheoremOneSubtheorems
    {P : TheoremOne.MaxProblemFamily.{u}}
    (h : DirectSavingsKarlssonBaseLowerPrimitiveCarrierTheoremOneSubtheorems P) :
    DirectSavingsPairwiseLowerPrimitiveCarrierTheoremOneSubtheorems P where
  upper_geometry := h.upper_geometry
  lower_pairwise :=
    h.lower_karlsson_base
      |>.toPairwiseCardinalityClusteredKarlssonBlowUpIncrementalLowerData

end DirectSavingsKarlssonBaseLowerPrimitiveCarrierTheoremOneSubtheorems

/-- Theorem 1 from primitive carrier direct savings plus Karlsson
four-base/local-blow-up lower construction data. -/
theorem theorem_one_from_direct_savings_karlsson_base_lower_primitive_carrier_subtheorems
    (P : TheoremOne.MaxProblemFamily.{u})
    (h : DirectSavingsKarlssonBaseLowerPrimitiveCarrierTheoremOneSubtheorems P) :
    TheoremOneStatement P := by
  exact theorem_one_from_direct_savings_pairwise_lower_primitive_carrier_subtheorems
    P h.toDirectSavingsPairwiseLowerPrimitiveCarrierTheoremOneSubtheorems

/-- Single-size formula from primitive carrier direct savings plus Karlsson
four-base/local-blow-up lower construction data. -/
theorem theorem_one_at_from_direct_savings_karlsson_base_lower_primitive_carrier_subtheorems
    (P : TheoremOne.MaxProblemFamily.{u})
    (h : DirectSavingsKarlssonBaseLowerPrimitiveCarrierTheoremOneSubtheorems P)
    (n : Nat) :
    P.aLop n =
      4 * ((n.choose 2 : Nat) : Rat) + manuscriptS n + (n : Rat) + 1 := by
  exact
    theorem_one_from_direct_savings_karlsson_base_lower_primitive_carrier_subtheorems
      P h n

end TheoremOneManuscript
end Lollipop
