import Lollipop.Final.TheoremOne

/-!
Expected-failure endpoint for the primitive-overlap plus indexed-point
geometry boundary.

Run with:

```sh
lake env lean expected_fail/MissingPrimitiveOverlapIndexedPointGeometryCertificates.lean
```

This file should fail because the two remaining construction-facing geometry
producers named below are intentionally not defined.
-/

namespace Lollipop
namespace Final

noncomputable section

/-- Once these two missing geometric producers are supplied, the most
construction-facing public endpoint has no remaining theorem-assembly gap. -/
noncomputable def primitiveOverlapIndexedPointGeometryCertificates
    (P : TheoremOne.MaxProblemFamily.{u}) :
    PrimitiveOverlapIndexedPointGeometryCertificates P := by
  exact
    { upper :=
        unformalized_primitive_overlap_upper_geometry P
      lower :=
        unformalized_indexed_point_karlsson_lower_geometry P }

/-- The no-missing-geometry primitive-overlap/indexed-point Theorem 1
endpoint. -/
theorem theorem_one_without_missing_primitive_overlap_indexed_point_geometry
    (P : TheoremOne.MaxProblemFamily.{u}) :
    TheoremOneStatement P :=
  theorem_one_from_primitive_overlap_indexed_lower P
    (primitiveOverlapIndexedPointGeometryCertificates P)

/-- The unfolded single-size formula from the primitive-overlap/indexed-point
endpoint. -/
theorem displayed_formula_without_missing_primitive_overlap_indexed_point_geometry
    (P : TheoremOne.MaxProblemFamily.{u}) (n : Nat) :
    P.aLop n =
      4 * ((n.choose 2 : Nat) : Rat) +
        TheoremOneManuscript.manuscriptS n + (n : Rat) + 1 :=
  displayed_formula_from_primitive_overlap_indexed_lower P
    (primitiveOverlapIndexedPointGeometryCertificates P) n

end

end Final
end Lollipop
