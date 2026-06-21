import Lollipop.Internal.Manuscript.Construction.AutomaticCardinalityWitness
import Lollipop.Internal.Manuscript.EndToEndFormalization.OverlapUpper
import Lollipop.Internal.Manuscript.FormalizedProof.FinalTheorem

/-!
Final public Theorem 1 endpoint.

This is the file to read first.  It exposes one theorem statement, one
geometry-certificate structure, and the theorem proving the displayed
lollipop formula from those certificates.

The certificate structure is deliberately manuscript-shaped:

* the upper field is primitive Euclidean lollipop carrier data with direct
  whole-carrier savings for the close/intriguing cases;
* the lower field is Karlsson's four-base table together with the local
  blow-up and ordered-insertion data.

Everything after those two geometric inputs is proved in the imported Lean
proof machinery.
-/

namespace Lollipop
namespace Final

universe u

/-! ## Statement -/

/-- Manuscript Theorem 1 in the displayed formula form. -/
abbrev TheoremOneStatement
    (P : TheoremOne.MaxProblemFamily.{u}) : Prop :=
  TheoremOneManuscript.FormalizedProof.FinalTheoremOneStatement P

/-- Single-size displayed formula from Theorem 1. -/
abbrev TheoremOneAtStatement
    (P : TheoremOne.MaxProblemFamily.{u}) (n : Nat) : Prop :=
  TheoremOneManuscript.FormalizedProof.FinalTheoremOneAtStatement P n

/-- The theorem statement is definitionally the pointwise displayed formula. -/
theorem theoremOneStatement_iff
    (P : TheoremOne.MaxProblemFamily.{u}) :
    TheoremOneStatement P ↔ ∀ n : Nat, TheoremOneAtStatement P n := by
  rfl

/-! ## Geometric certificate boundary -/

/-- The final geometry boundary closest to the current manuscript proof.

This is the only public certificate package needed by the final theorem
endpoint.  Supplying these two fields for the intended lollipop problem
family completes the remaining Euclidean/model-specific part of the proof.
-/
structure GeometryCertificates
    (P : TheoremOne.MaxProblemFamily.{u}) : Type u where
  upper :
    TheoremOneManuscript.PrimitiveGeometry.PrimitiveCarrierDirectSavingsUpperGeometryData
      P.toProblemFamily
  lower :
    TheoremOneManuscript.ExplicitInputs.KarlssonBaseBlowUpIncrementalLowerData
      P.toProblemFamily

/-- A weaker lower-bound-facing geometry boundary.

The upper side is the same direct whole-carrier savings package.  The lower
side asks only for pairwise Karlsson lower bounds, not an exact classification
of every blow-up carrier intersection.  This is often the more natural target
for perturbation constructions: produce enough certified intersection points,
then Lean performs the finite summation and maximum argument. -/
structure MonotoneGeometryCertificates
    (P : TheoremOne.MaxProblemFamily.{u}) : Type u where
  upper :
    TheoremOneManuscript.PrimitiveGeometry.PrimitiveCarrierDirectSavingsUpperGeometryData
      P.toProblemFamily
  lower :
    TheoremOneManuscript.ExplicitInputs.PairwiseCardinalityClusteredKarlssonBlowUpIncrementalLowerBoundData
      P.toProblemFamily

/-- Constructive lower-bound-facing geometry boundary.

The lower field asks for explicit indexed carrier-intersection points for
each sorted Karlsson blow-up pair.  Lean proves from those points that the
automatic carrier finset has the required cardinality, then converts that
cardinality fact to the monotone lower theorem endpoint. -/
structure IndexedPointLowerGeometryCertificates
    (P : TheoremOne.MaxProblemFamily.{u}) : Type u where
  upper :
    TheoremOneManuscript.PrimitiveGeometry.PrimitiveCarrierDirectSavingsUpperGeometryData
      P.toProblemFamily
  lower :
    TheoremOneManuscript.ConstructionFormalization.StepwiseCanonicalKarlssonIndexedPointLowerCertificate
      P.toProblemFamily

/-- Component-indexed constructive lower-bound-facing geometry boundary.

The lower field lets the Karlsson construction provide separate indexed
point families for the four primitive component intersections.  Lean assembles
their disjoint union into the monolithic indexed lower-point certificate. -/
structure ComponentIndexedPointLowerGeometryCertificates
    (P : TheoremOne.MaxProblemFamily.{u}) : Type u where
  upper :
    TheoremOneManuscript.PrimitiveGeometry.PrimitiveCarrierDirectSavingsUpperGeometryData
      P.toProblemFamily
  lower :
    TheoremOneManuscript.ConstructionFormalization.StepwiseCanonicalKarlssonComponentIndexedPointLowerCertificate
      P.toProblemFamily

/-- Most construction-facing public boundary currently exposed.

The upper field asks for primitive coordinate overlap witnesses for the
close/intriguing savings branches.  The lower field asks for explicit indexed
carrier-intersection points.  Lean converts both to the direct-savings plus
monotone lower endpoint. -/
structure PrimitiveOverlapIndexedPointGeometryCertificates
    (P : TheoremOne.MaxProblemFamily.{u}) : Type u where
  upper :
    TheoremOneManuscript.EndToEndFormalization.OverlapUpper.PrimitiveFlexibleOverlapSavingsStepwiseCertificate
      P.toProblemFamily
  lower :
    TheoremOneManuscript.ConstructionFormalization.StepwiseCanonicalKarlssonIndexedPointLowerCertificate
      P.toProblemFamily

/-- Primitive-overlap upper plus component-indexed lower boundary.

This is the most coordinate-facing public certificate boundary: the upper side
is given by raw primitive overlap witnesses, and the lower side is given by
separate component-indexed Karlsson point families. -/
structure PrimitiveOverlapComponentIndexedPointGeometryCertificates
    (P : TheoremOne.MaxProblemFamily.{u}) : Type u where
  upper :
    TheoremOneManuscript.EndToEndFormalization.OverlapUpper.PrimitiveFlexibleOverlapSavingsStepwiseCertificate
      P.toProblemFamily
  lower :
    TheoremOneManuscript.ConstructionFormalization.StepwiseCanonicalKarlssonComponentIndexedPointLowerCertificate
      P.toProblemFamily

namespace GeometryCertificates

/-- Convert the public certificate boundary to the internal theorem package. -/
noncomputable def toSubtheorems
    {P : TheoremOne.MaxProblemFamily.{u}}
    (h : GeometryCertificates P) :
    TheoremOneManuscript.FormalizedProof.DirectSavingsKarlssonBaseLowerTheoremOneSubtheorems
      P where
  upper_geometry := h.upper
  lower_karlsson_base := h.lower

end GeometryCertificates

namespace MonotoneGeometryCertificates

/-- Convert the monotone public certificate boundary to the internal theorem
package. -/
noncomputable def toSubtheorems
    {P : TheoremOne.MaxProblemFamily.{u}}
    (h : MonotoneGeometryCertificates P) :
    TheoremOneManuscript.FormalizedProof.DirectSavingsMonotonePairwiseLowerTheoremOneSubtheorems
      P where
  upper_geometry := h.upper
  lower_pairwise_bound := h.lower

end MonotoneGeometryCertificates

namespace IndexedPointLowerGeometryCertificates

/-- Convert explicit indexed lower points to the monotone final certificate
boundary. -/
noncomputable def toMonotoneGeometryCertificates
    {P : TheoremOne.MaxProblemFamily.{u}}
    (h : IndexedPointLowerGeometryCertificates P) :
    MonotoneGeometryCertificates P where
  upper := h.upper
  lower :=
    h.lower
      |>.toStepwiseCanonicalKarlssonCarrierCardLowerCertificate
      |>.toStepwisePairLocalKarlssonLowerBoundCertificate
      |>.toPairwiseCardinalityClusteredKarlssonBlowUpIncrementalLowerBoundData

end IndexedPointLowerGeometryCertificates

namespace ComponentIndexedPointLowerGeometryCertificates

/-- Convert component-indexed lower points to the indexed lower public
certificate boundary. -/
noncomputable def toIndexedPointLowerGeometryCertificates
    {P : TheoremOne.MaxProblemFamily.{u}}
    (h : ComponentIndexedPointLowerGeometryCertificates P) :
    IndexedPointLowerGeometryCertificates P where
  upper := h.upper
  lower := h.lower.toStepwiseCanonicalKarlssonIndexedPointLowerCertificate

end ComponentIndexedPointLowerGeometryCertificates

namespace PrimitiveOverlapIndexedPointGeometryCertificates

/-- Convert primitive overlap witnesses and indexed lower points to the
indexed lower public certificate boundary. -/
noncomputable def toIndexedPointLowerGeometryCertificates
    {P : TheoremOne.MaxProblemFamily.{u}}
    (h : PrimitiveOverlapIndexedPointGeometryCertificates P) :
    IndexedPointLowerGeometryCertificates P where
  upper :=
    h.upper
      |>.toOverlapSavingsStepwiseCertificate
      |>.toDirectSavingsStepwiseCertificate
      |>.toDirectSavingsUpperGeometryData
  lower := h.lower

end PrimitiveOverlapIndexedPointGeometryCertificates

namespace PrimitiveOverlapComponentIndexedPointGeometryCertificates

/-- Convert primitive overlap witnesses and component-indexed lower points to
the primitive-overlap/indexed-lower public certificate boundary. -/
noncomputable def toPrimitiveOverlapIndexedPointGeometryCertificates
    {P : TheoremOne.MaxProblemFamily.{u}}
    (h : PrimitiveOverlapComponentIndexedPointGeometryCertificates P) :
    PrimitiveOverlapIndexedPointGeometryCertificates P where
  upper := h.upper
  lower := h.lower.toStepwiseCanonicalKarlssonIndexedPointLowerCertificate

/-- Forget primitive overlap witnesses after converting them to direct upper
savings, retaining the component-indexed lower boundary. -/
noncomputable def toComponentIndexedPointLowerGeometryCertificates
    {P : TheoremOne.MaxProblemFamily.{u}}
    (h : PrimitiveOverlapComponentIndexedPointGeometryCertificates P) :
    ComponentIndexedPointLowerGeometryCertificates P where
  upper :=
    h.upper
      |>.toOverlapSavingsStepwiseCertificate
      |>.toDirectSavingsStepwiseCertificate
      |>.toDirectSavingsUpperGeometryData
  lower := h.lower

end PrimitiveOverlapComponentIndexedPointGeometryCertificates

/-! ## Theorem 1 -/

/-- Manuscript Theorem 1 from the final geometric certificate boundary. -/
theorem theorem_one
    (P : TheoremOne.MaxProblemFamily.{u})
    (h : GeometryCertificates P) :
    TheoremOneStatement P :=
  TheoremOneManuscript.FormalizedProof.theorem_one_from_direct_savings_karlsson_base_lower_subtheorems
    P h.toSubtheorems

/-- Manuscript Theorem 1 from the monotone lower-bound geometry boundary. -/
theorem theorem_one_from_monotone
    (P : TheoremOne.MaxProblemFamily.{u})
    (h : MonotoneGeometryCertificates P) :
    TheoremOneStatement P :=
  TheoremOneManuscript.FormalizedProof.theorem_one_from_direct_savings_monotone_pairwise_lower_subtheorems
    P h.toSubtheorems

/-- Manuscript Theorem 1 from explicit indexed lower points. -/
theorem theorem_one_from_indexed_lower
    (P : TheoremOne.MaxProblemFamily.{u})
    (h : IndexedPointLowerGeometryCertificates P) :
    TheoremOneStatement P :=
  theorem_one_from_monotone P h.toMonotoneGeometryCertificates

/-- Manuscript Theorem 1 from component-indexed explicit lower points. -/
theorem theorem_one_from_component_indexed_lower
    (P : TheoremOne.MaxProblemFamily.{u})
    (h : ComponentIndexedPointLowerGeometryCertificates P) :
    TheoremOneStatement P :=
  theorem_one_from_indexed_lower P h.toIndexedPointLowerGeometryCertificates

/-- Manuscript Theorem 1 from primitive upper overlap witnesses and explicit
indexed lower points. -/
theorem theorem_one_from_primitive_overlap_indexed_lower
    (P : TheoremOne.MaxProblemFamily.{u})
    (h : PrimitiveOverlapIndexedPointGeometryCertificates P) :
    TheoremOneStatement P :=
  theorem_one_from_indexed_lower P h.toIndexedPointLowerGeometryCertificates

/-- Manuscript Theorem 1 from primitive upper overlap witnesses and
component-indexed explicit lower points. -/
theorem theorem_one_from_primitive_overlap_component_indexed_lower
    (P : TheoremOne.MaxProblemFamily.{u})
    (h : PrimitiveOverlapComponentIndexedPointGeometryCertificates P) :
    TheoremOneStatement P :=
  theorem_one_from_primitive_overlap_indexed_lower P
    h.toPrimitiveOverlapIndexedPointGeometryCertificates

/-- Single-size Theorem 1 from the final geometric certificate boundary. -/
theorem theorem_one_at
    (P : TheoremOne.MaxProblemFamily.{u})
    (h : GeometryCertificates P)
    (n : Nat) :
    TheoremOneAtStatement P n :=
  theorem_one P h n

/-- Single-size Theorem 1 from the monotone lower-bound geometry boundary. -/
theorem theorem_one_at_from_monotone
    (P : TheoremOne.MaxProblemFamily.{u})
    (h : MonotoneGeometryCertificates P)
    (n : Nat) :
    TheoremOneAtStatement P n :=
  theorem_one_from_monotone P h n

/-- Single-size Theorem 1 from explicit indexed lower points. -/
theorem theorem_one_at_from_indexed_lower
    (P : TheoremOne.MaxProblemFamily.{u})
    (h : IndexedPointLowerGeometryCertificates P)
    (n : Nat) :
    TheoremOneAtStatement P n :=
  theorem_one_from_indexed_lower P h n

/-- Single-size Theorem 1 from component-indexed explicit lower points. -/
theorem theorem_one_at_from_component_indexed_lower
    (P : TheoremOne.MaxProblemFamily.{u})
    (h : ComponentIndexedPointLowerGeometryCertificates P)
    (n : Nat) :
    TheoremOneAtStatement P n :=
  theorem_one_from_component_indexed_lower P h n

/-- Single-size Theorem 1 from primitive upper overlap witnesses and explicit
indexed lower points. -/
theorem theorem_one_at_from_primitive_overlap_indexed_lower
    (P : TheoremOne.MaxProblemFamily.{u})
    (h : PrimitiveOverlapIndexedPointGeometryCertificates P)
    (n : Nat) :
    TheoremOneAtStatement P n :=
  theorem_one_from_primitive_overlap_indexed_lower P h n

/-- Single-size Theorem 1 from primitive upper overlap witnesses and
component-indexed explicit lower points. -/
theorem theorem_one_at_from_primitive_overlap_component_indexed_lower
    (P : TheoremOne.MaxProblemFamily.{u})
    (h : PrimitiveOverlapComponentIndexedPointGeometryCertificates P)
    (n : Nat) :
    TheoremOneAtStatement P n :=
  theorem_one_from_primitive_overlap_component_indexed_lower P h n

/-- The fully unfolded single-size displayed formula:
`a_Lop(n) = 4 * binom(n,2) + S(n) + n + 1`. -/
theorem displayed_formula
    (P : TheoremOne.MaxProblemFamily.{u})
    (h : GeometryCertificates P)
    (n : Nat) :
    P.aLop n =
      4 * ((n.choose 2 : Nat) : Rat) +
        TheoremOneManuscript.manuscriptS n + (n : Rat) + 1 :=
  theorem_one_at P h n

/-- Fully unfolded single-size displayed formula from the monotone
lower-bound geometry boundary. -/
theorem displayed_formula_from_monotone
    (P : TheoremOne.MaxProblemFamily.{u})
    (h : MonotoneGeometryCertificates P)
    (n : Nat) :
    P.aLop n =
      4 * ((n.choose 2 : Nat) : Rat) +
        TheoremOneManuscript.manuscriptS n + (n : Rat) + 1 :=
  theorem_one_at_from_monotone P h n

/-- Fully unfolded single-size displayed formula from explicit indexed lower
points. -/
theorem displayed_formula_from_indexed_lower
    (P : TheoremOne.MaxProblemFamily.{u})
    (h : IndexedPointLowerGeometryCertificates P)
    (n : Nat) :
    P.aLop n =
      4 * ((n.choose 2 : Nat) : Rat) +
        TheoremOneManuscript.manuscriptS n + (n : Rat) + 1 :=
  theorem_one_at_from_indexed_lower P h n

/-- Fully unfolded single-size displayed formula from component-indexed
explicit lower points. -/
theorem displayed_formula_from_component_indexed_lower
    (P : TheoremOne.MaxProblemFamily.{u})
    (h : ComponentIndexedPointLowerGeometryCertificates P)
    (n : Nat) :
    P.aLop n =
      4 * ((n.choose 2 : Nat) : Rat) +
        TheoremOneManuscript.manuscriptS n + (n : Rat) + 1 :=
  theorem_one_at_from_component_indexed_lower P h n

/-- Fully unfolded single-size displayed formula from primitive upper overlap
witnesses and explicit indexed lower points. -/
theorem displayed_formula_from_primitive_overlap_indexed_lower
    (P : TheoremOne.MaxProblemFamily.{u})
    (h : PrimitiveOverlapIndexedPointGeometryCertificates P)
    (n : Nat) :
    P.aLop n =
      4 * ((n.choose 2 : Nat) : Rat) +
        TheoremOneManuscript.manuscriptS n + (n : Rat) + 1 :=
  theorem_one_at_from_primitive_overlap_indexed_lower P h n

/-- Fully unfolded single-size displayed formula from primitive upper overlap
witnesses and component-indexed explicit lower points. -/
theorem displayed_formula_from_primitive_overlap_component_indexed_lower
    (P : TheoremOne.MaxProblemFamily.{u})
    (h : PrimitiveOverlapComponentIndexedPointGeometryCertificates P)
    (n : Nat) :
    P.aLop n =
      4 * ((n.choose 2 : Nat) : Rat) +
        TheoremOneManuscript.manuscriptS n + (n : Rat) + 1 :=
  theorem_one_at_from_primitive_overlap_component_indexed_lower P h n

end Final
end Lollipop
