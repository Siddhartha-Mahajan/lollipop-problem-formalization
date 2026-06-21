# Lollipop End-to-End Formalization

This repository is the cleaned Lean handoff for the lollipop manuscript.
It has public theorem endpoints and explicit remaining geometry boundaries.

## Start Here

Open:

```lean
Lollipop/Final/TheoremOne.lean
```

The main public objects are:

```lean
Lollipop.Final.TheoremOneStatement
Lollipop.Final.TheoremOneAtStatement
Lollipop.Final.GeometryCertificates
Lollipop.Final.MonotoneGeometryCertificates
Lollipop.Final.IndexedPointLowerGeometryCertificates
Lollipop.Final.ComponentIndexedPointLowerGeometryCertificates
Lollipop.Final.PrimitiveOverlapIndexedPointGeometryCertificates
Lollipop.Final.PrimitiveOverlapComponentIndexedPointGeometryCertificates
Lollipop.Final.theorem_one
Lollipop.Final.displayed_formula
Lollipop.Final.theorem_one_from_monotone
Lollipop.Final.displayed_formula_from_monotone
Lollipop.Final.theorem_one_from_indexed_lower
Lollipop.Final.displayed_formula_from_indexed_lower
Lollipop.Final.theorem_one_from_component_indexed_lower
Lollipop.Final.displayed_formula_from_component_indexed_lower
Lollipop.Final.theorem_one_from_primitive_overlap_indexed_lower
Lollipop.Final.displayed_formula_from_primitive_overlap_indexed_lower
Lollipop.Final.theorem_one_from_primitive_overlap_component_indexed_lower
Lollipop.Final.displayed_formula_from_primitive_overlap_component_indexed_lower
```

The theorem endpoint is:

```lean
theorem Lollipop.Final.theorem_one
    (P : TheoremOne.MaxProblemFamily)
    (h : Lollipop.Final.GeometryCertificates P) :
    Lollipop.Final.TheoremOneStatement P
```

The unfolded formula endpoint is:

```lean
theorem Lollipop.Final.displayed_formula
    (P : TheoremOne.MaxProblemFamily)
    (h : Lollipop.Final.GeometryCertificates P)
    (n : Nat) :
    P.aLop n =
      4 * ((n.choose 2 : Nat) : Rat) +
        TheoremOneManuscript.manuscriptS n + (n : Rat) + 1
```

## What Lean Proves

Lean proves the algebraic, finite, combinatorial, colored-Turan, matrix,
carrier-counting, lower-bound summation, and theorem-assembly parts after a
geometric certificate boundary is supplied.

The exact public certificate boundary is:

```lean
structure Lollipop.Final.GeometryCertificates
    (P : TheoremOne.MaxProblemFamily) where
  upper :
    PrimitiveCarrierDirectSavingsUpperGeometryData P.toProblemFamily
  lower :
    KarlssonBaseBlowUpIncrementalLowerData P.toProblemFamily
```

In words, the remaining inputs are:

- an upper certificate giving direct whole-carrier savings for the
  close/intriguing primitive Euclidean lollipop cases;
- a lower certificate giving Karlsson's four-base table, the local blow-up
  arrangements, and ordered-insertion data.

Once those two fields are present, `Lollipop.Final.theorem_one` proves the
manuscript Theorem 1 formula.

There is also a lower-bound-facing endpoint:

```lean
structure Lollipop.Final.MonotoneGeometryCertificates
    (P : TheoremOne.MaxProblemFamily) where
  upper :
    PrimitiveCarrierDirectSavingsUpperGeometryData P.toProblemFamily
  lower :
    PairwiseCardinalityClusteredKarlssonBlowUpIncrementalLowerBoundData
      P.toProblemFamily
```

This version keeps the same upper geometry requirement but weakens the lower
side to pairwise Karlsson lower bounds.  For a perturbation construction this
is often the more natural target: supply enough certified carrier-intersection
points, and Lean performs the summation and theorem assembly.

The most constructive lower endpoint is:

```lean
structure Lollipop.Final.IndexedPointLowerGeometryCertificates
    (P : TheoremOne.MaxProblemFamily) where
  upper :
    PrimitiveCarrierDirectSavingsUpperGeometryData P.toProblemFamily
  lower :
    StepwiseCanonicalKarlssonIndexedPointLowerCertificate P.toProblemFamily
```

Here the lower construction supplies explicit indexed points in each carrier
intersection, plus injectivity, membership, noncoincidence, automatic
pair-table agreement, and ordered insertion data.  Lean converts those points
to the monotone pairwise lower boundary.

There is also a component-indexed lower endpoint:

```lean
structure Lollipop.Final.ComponentIndexedPointLowerGeometryCertificates
    (P : TheoremOne.MaxProblemFamily) where
  upper :
    PrimitiveCarrierDirectSavingsUpperGeometryData P.toProblemFamily
  lower :
    StepwiseCanonicalKarlssonComponentIndexedPointLowerCertificate
      P.toProblemFamily
```

Here the lower construction supplies separate indexed point families for the
four primitive components: circle-circle, circle-ray, ray-circle, and ray-ray.
Lean proves that the disjoint union has the canonical Karlsson lower size and
converts it to the indexed lower-point endpoint.

Internally, the stronger exact component-coverage certificate
`StepwiseCanonicalKarlssonIndexedDisjointComponentFinsetLowerCertificate`
also converts to this component-indexed lower endpoint.  Thus a coordinate
proof may either provide enough disjoint component lower points, or provide
exact component coverage and let Lean forget down to the lower-bound boundary.

The primitive-overlap/indexed-point endpoint is:

```lean
structure Lollipop.Final.PrimitiveOverlapIndexedPointGeometryCertificates
    (P : TheoremOne.MaxProblemFamily) where
  upper :
    PrimitiveFlexibleOverlapSavingsStepwiseCertificate P.toProblemFamily
  lower :
    StepwiseCanonicalKarlssonIndexedPointLowerCertificate P.toProblemFamily
```

Here the upper construction supplies raw primitive coordinate overlap
witnesses for the close, intriguing, and close-plus-intriguing branches, and
the lower construction supplies explicit indexed carrier-intersection points.
Lean converts this package to the final theorem.

The most coordinate-facing endpoint currently exposed is:

```lean
structure Lollipop.Final.PrimitiveOverlapComponentIndexedPointGeometryCertificates
    (P : TheoremOne.MaxProblemFamily) where
  upper :
    PrimitiveFlexibleOverlapSavingsStepwiseCertificate P.toProblemFamily
  lower :
    StepwiseCanonicalKarlssonComponentIndexedPointLowerCertificate
      P.toProblemFamily
```

This combines raw primitive upper overlap witnesses with component-indexed
Karlsson lower point families.  For a handoff to a geometry checker, this is
the closest Lean boundary to coordinate-by-coordinate verification.

## What Is Already Certified Geometrically

The proved base geometry is in:

```lean
Lollipop/Final/Geometry.lean
```

That file contains the exact OEIS/Karlsson four-lollipop base arrangement,
six pair coordinate-crossing certificates, the exceptional `(Q0,Q1)` routed
upper certificate, the canonical all-ones relabeling, and the base region
equation `45 = 40 + 4 + 1`.

These are base certificates.  They do not by themselves construct the all-`n`
upper savings certificate or the all-sorted-blow-up lower construction.

## Expected Failure File

The remaining geometry gap is isolated in:

```lean
expected_fail/MissingGeometryCertificates.lean
expected_fail/MissingMonotoneGeometryCertificates.lean
expected_fail/MissingIndexedPointGeometryCertificates.lean
expected_fail/MissingPrimitiveOverlapIndexedPointGeometryCertificates.lean
expected_fail/MissingPrimitiveOverlapComponentIndexedPointGeometryCertificates.lean
```

The exact lower endpoint intentionally fails at exactly these names:

```lean
unformalized_direct_savings_upper_geometry
unformalized_karlsson_base_blowup_lower_geometry
```

Those are the two constructors that would complete the no-missing-geometry
endpoint:

```lean
Lollipop.Final.theorem_one_without_missing_geometry
Lollipop.Final.displayed_formula_without_missing_geometry
```

The monotone lower endpoint intentionally fails at:

```lean
unformalized_direct_savings_upper_geometry
unformalized_monotone_pairwise_karlsson_lower_geometry
```

That second lower constructor is weaker than the exact Karlsson-base
constructor: it only has to produce pairwise lower bounds and ordered
region-increment data.

The indexed-point lower endpoint intentionally fails at:

```lean
unformalized_direct_savings_upper_geometry
unformalized_indexed_point_karlsson_lower_geometry
```

This is the constructive lower target for formalizing Karlsson's perturbation
argument by explicit carrier-intersection points.

The component-indexed lower endpoint intentionally fails at:

```lean
unformalized_direct_savings_upper_geometry
unformalized_component_indexed_point_karlsson_lower_geometry
```

This is the same lower target split across the four primitive component
intersections.

The primitive-overlap/indexed-point endpoint intentionally fails at:

```lean
unformalized_primitive_overlap_upper_geometry
unformalized_indexed_point_karlsson_lower_geometry
```

This is the closest public boundary to a coordinate-by-coordinate completion:
prove Paulsen-style upper overlap witnesses and Karlsson indexed lower points.

The primitive-overlap/component-indexed endpoint intentionally fails at:

```lean
unformalized_primitive_overlap_upper_geometry
unformalized_component_indexed_point_karlsson_lower_geometry
```

This is the most coordinate-facing expected-fail endpoint: prove Paulsen-style
upper overlap witnesses and Karlsson component-indexed lower point families.

Run it with:

```sh
lake env lean expected_fail/MissingGeometryCertificates.lean
lake env lean expected_fail/MissingMonotoneGeometryCertificates.lean
lake env lean expected_fail/MissingIndexedPointGeometryCertificates.lean
lake env lean expected_fail/MissingPrimitiveOverlapIndexedPointGeometryCertificates.lean
lake env lean expected_fail/MissingPrimitiveOverlapComponentIndexedPointGeometryCertificates.lean
```

The expected result is unknown-identifier errors at the names above.

## Repository Layout

```text
Lollipop.lean
Lollipop/Final.lean
Lollipop/Final/TheoremOne.lean
Lollipop/Final/Geometry.lean
Lollipop/Final/GeometryObstruction.lean
Lollipop/Internal/
expected_fail/MissingGeometryCertificates.lean
expected_fail/MissingMonotoneGeometryCertificates.lean
expected_fail/MissingIndexedPointGeometryCertificates.lean
expected_fail/MissingPrimitiveOverlapIndexedPointGeometryCertificates.lean
expected_fail/MissingPrimitiveOverlapComponentIndexedPointGeometryCertificates.lean
manuscript/
references/
lakefile.lean
lake-manifest.json
lean-toolchain
```

`Lollipop/Final/` is the public surface.  `Lollipop/Internal/` is the proof
closure required by the final endpoint; it is not a collection of competing
final theorem statements.

`Lollipop/Final/GeometryObstruction.lean` proves that the final certificate
boundary cannot be filled polymorphically for every abstract
`MaxProblemFamily`; the remaining constructors must target the intended
concrete lollipop family or assume genuine Euclidean realization data.

`manuscript/current/` contains the current TeX/PDF manuscript copy.
`manuscript/original/` contains the original manuscript source copied from
`A_Colored_Turan_Proof_of_the_Lollipop_Formula`.

`references/` contains the local problem statement, investigation notes,
cached OEIS/source pages, and the Sloane/CKS reference PDFs used to orient the
geometric certificate work.

## Verification

Build the final formalization:

```sh
lake build Lollipop
```

On this machine, the first fresh build of this repository from an empty
`.lake/` cache took about 25 minutes, including cloning and compiling mathlib
dependencies.  After the local `.lake/` cache existed, rerunning
`lake build Lollipop` took 4.11 seconds.

Build only the public final endpoint:

```sh
lake build Lollipop.Final
```

Check the intentional geometry failure:

```sh
lake env lean expected_fail/MissingGeometryCertificates.lean
```

There should be no `sorry`, `admit`, or custom `axiom` in the Lean files
included here.
