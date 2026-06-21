import Lollipop.Final.TheoremOne

/-!
Expected-failure endpoint for the weaker monotone lower geometry boundary.

Run with:

```sh
lake env lean expected_fail/MissingMonotoneGeometryCertificates.lean
```

This file should fail because the two remaining geometric producers named
below are intentionally not defined.
-/

namespace Lollipop
namespace Final

noncomputable section

/-- Once these two missing geometric producers are supplied, the monotone
lower-bound final endpoint has no remaining theorem-assembly gap. -/
noncomputable def monotoneGeometryCertificates
    (P : TheoremOne.MaxProblemFamily.{u}) :
    MonotoneGeometryCertificates P := by
  exact
    { upper :=
        unformalized_direct_savings_upper_geometry P
      lower :=
        unformalized_monotone_pairwise_karlsson_lower_geometry P }

/-- The no-missing-geometry monotone Theorem 1 endpoint. -/
theorem theorem_one_without_missing_monotone_geometry
    (P : TheoremOne.MaxProblemFamily.{u}) :
    TheoremOneStatement P :=
  theorem_one_from_monotone P (monotoneGeometryCertificates P)

/-- The unfolded single-size formula from the monotone endpoint. -/
theorem displayed_formula_without_missing_monotone_geometry
    (P : TheoremOne.MaxProblemFamily.{u}) (n : Nat) :
    P.aLop n =
      4 * ((n.choose 2 : Nat) : Rat) +
        TheoremOneManuscript.manuscriptS n + (n : Rat) + 1 :=
  displayed_formula_from_monotone P (monotoneGeometryCertificates P) n

end

end Final
end Lollipop
