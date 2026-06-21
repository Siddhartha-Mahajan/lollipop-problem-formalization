import Lollipop.Final

/-!
Expected-failure endpoint for the remaining geometry.

This file is intentionally outside the `Lollipop` library build.  Run

```sh
lake env lean expected_fail/MissingGeometryCertificates.lean
```

to see the exact current gap.

The buildable final theorem endpoint is
`Lollipop.Final.theorem_one`.  It proves the displayed Theorem 1 formula from
one certificate package:

```lean
Lollipop.Final.GeometryCertificates P
```

That package has two fields:

* direct whole-carrier upper savings for primitive Euclidean lollipop
  carriers, and
* Karlsson four-base/local-blow-up lower construction data.

The concrete OEIS/Karlsson four-base geometry already proved in Lean is
available from `Lollipop.Final.Geometry`, but the all-`n` Euclidean upper
savings and blow-up construction are still not formalized.  The two unknown
constructors below mark exactly where those missing certificates would be
inserted.
-/

namespace Lollipop
namespace Final

universe u

/-- Intentionally failing constructor for the final manuscript-shaped
geometry-certificate boundary. -/
noncomputable def geometryCertificates
    (P : TheoremOne.MaxProblemFamily.{u}) :
    GeometryCertificates P := by
  exact
    { upper :=
        unformalized_direct_savings_upper_geometry P
      lower :=
        unformalized_karlsson_base_blowup_lower_geometry
          oeisBaseLowerGeometryCertificates
          oeisCanonicalAllOnesGeometryCertificates
          P }

/-- This is the no-missing-geometry Theorem 1 endpoint once the two
constructors above are supplied.  Today this file fails at
`geometryCertificates`. -/
theorem theorem_one_without_missing_geometry
    (P : TheoremOne.MaxProblemFamily.{u}) :
    TheoremOneStatement P :=
  theorem_one P (geometryCertificates P)

/-- Fully unfolded single-size formula from the same missing geometry. -/
theorem displayed_formula_without_missing_geometry
    (P : TheoremOne.MaxProblemFamily.{u})
    (n : Nat) :
    P.aLop n =
      4 * ((n.choose 2 : Nat) : Rat) +
        TheoremOneManuscript.manuscriptS n + (n : Rat) + 1 :=
  displayed_formula P (geometryCertificates P) n

end Final
end Lollipop
