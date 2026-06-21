import Lollipop.Final.TheoremOne

/-!
Expected-failure endpoint for the indexed-point lower geometry boundary.

Run with:

```sh
lake env lean expected_fail/MissingIndexedPointGeometryCertificates.lean
```

This file should fail because the two remaining geometric producers named
below are intentionally not defined.
-/

namespace Lollipop
namespace Final

noncomputable section

/-- Once these two missing geometric producers are supplied, the explicit
indexed-point lower endpoint has no remaining theorem-assembly gap. -/
noncomputable def indexedPointLowerGeometryCertificates
    (P : TheoremOne.MaxProblemFamily.{u}) :
    IndexedPointLowerGeometryCertificates P := by
  exact
    { upper :=
        unformalized_direct_savings_upper_geometry P
      lower :=
        unformalized_indexed_point_karlsson_lower_geometry P }

/-- The no-missing-geometry indexed-point Theorem 1 endpoint. -/
theorem theorem_one_without_missing_indexed_point_geometry
    (P : TheoremOne.MaxProblemFamily.{u}) :
    TheoremOneStatement P :=
  theorem_one_from_indexed_lower P (indexedPointLowerGeometryCertificates P)

/-- The unfolded single-size formula from the indexed-point endpoint. -/
theorem displayed_formula_without_missing_indexed_point_geometry
    (P : TheoremOne.MaxProblemFamily.{u}) (n : Nat) :
    P.aLop n =
      4 * ((n.choose 2 : Nat) : Rat) +
        TheoremOneManuscript.manuscriptS n + (n : Rat) + 1 :=
  displayed_formula_from_indexed_lower P
    (indexedPointLowerGeometryCertificates P) n

end

end Final
end Lollipop
