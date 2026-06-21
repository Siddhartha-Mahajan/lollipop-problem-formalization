# Lollipop End-to-End Formalization

This repository is the cleaned Lean handoff for the lollipop manuscript.
Lean proves the theorem assembly once the remaining Euclidean geometry
certificates are supplied.

## Start Here

Read this file first:

```lean
Lollipop/Final/TheoremOne.lean
```

The main public theorem endpoint is:

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

For coordinate-by-coordinate geometry work, the most useful public endpoint is:

```lean
Lollipop.Final.PrimitiveOverlapComponentIndexedPointGeometryCertificates
Lollipop.Final.theorem_one_from_primitive_overlap_component_indexed_lower
Lollipop.Final.displayed_formula_from_primitive_overlap_component_indexed_lower
```

## What Lean Proves

Lean proves the algebraic, finite, combinatorial, colored-Turan, matrix,
carrier-counting, lower-bound summation, and theorem-assembly parts.

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
- a lower certificate giving Karlsson's four-base table, local blow-up
  arrangements, and ordered-insertion region data.

Once those two fields are present, `Lollipop.Final.theorem_one` proves the
manuscript Theorem 1 formula.

## Geometry Work

The proved base geometry is in:

```lean
Lollipop/Final/Geometry.lean
```

That file contains the exact OEIS/Karlsson four-lollipop base arrangement,
the six pair coordinate-crossing certificates, the exceptional `(Q0,Q1)`
routed upper certificate, the canonical all-ones relabeling, and the base
region equation `45 = 40 + 4 + 1`.

These are base certificates.  They do not by themselves construct:

- the all-`n` upper savings certificate;
- the all-sorted-blow-up Karlsson lower construction.

For the current geometry formalization work, the most coordinate-facing split
is:

```lean
upper :
  PrimitiveFlexibleOverlapSavingsStepwiseCertificate P.toProblemFamily

lower :
  StepwiseCanonicalKarlssonComponentIndexedPointLowerCertificate
    P.toProblemFamily
```

This asks the geometry proof to supply:

- raw primitive overlap witnesses for the close, intriguing, and
  close-plus-intriguing upper branches;
- separate Karlsson lower point families for the four primitive components:
  circle-circle, circle-ray, ray-circle, and ray-ray.

Lean then converts those data to the direct-savings and monotone lower
boundaries used by the final theorem.

Relevant helper code:

```lean
Lollipop/Internal/Manuscript/EndToEndFormalization/OverlapUpper.lean
Lollipop/Internal/Manuscript/Construction/AutomaticCardinalityWitness.lean
Lollipop/Internal/Manuscript/Construction/IndexedCarrier.lean
```

The overlap helper layer includes orientation adapters such as `symm` and
`ofEither` for raw primitive overlap witnesses, plus lifted component-overlap
orientation helpers.  These are infrastructure for certificate writing; they
are not additional theorem endpoints.

## Expected Failures

The remaining geometry gap is intentionally isolated in:

```lean
expected_fail/MissingGeometryCertificates.lean
expected_fail/MissingMonotoneGeometryCertificates.lean
expected_fail/MissingIndexedPointGeometryCertificates.lean
expected_fail/MissingPrimitiveOverlapIndexedPointGeometryCertificates.lean
expected_fail/MissingPrimitiveOverlapComponentIndexedPointGeometryCertificates.lean
```

The most important expected-failure endpoint for current coordinate geometry
work is:

```lean
expected_fail/MissingPrimitiveOverlapComponentIndexedPointGeometryCertificates.lean
```

It fails at these two missing producers:

```lean
unformalized_primitive_overlap_upper_geometry
unformalized_component_indexed_point_karlsson_lower_geometry
```

Supplying those two producers would complete the most coordinate-facing
Theorem 1 endpoint.  The other expected-failure files expose older or weaker
certificate boundaries.

Run the current coordinate-facing failure with:

```sh
lake env lean expected_fail/MissingPrimitiveOverlapComponentIndexedPointGeometryCertificates.lean
```

The expected result is unknown-identifier errors at the missing geometry
producer names.

## Repository Layout

```text
Lollipop.lean
Lollipop/Final.lean
Lollipop/Final/TheoremOne.lean
Lollipop/Final/Geometry.lean
Lollipop/Final/GeometryObstruction.lean
Lollipop/Internal/
expected_fail/
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
`MaxProblemFamily`.  The remaining geometry constructors must target the
intended concrete lollipop family or assume genuine Euclidean realization
data.

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
dependencies.  After the local `.lake/` cache existed, a no-op
`lake build Lollipop` on the current tree took 3.83 seconds.

Build only the public final endpoint:

```sh
lake build Lollipop.Final
```

There should be no `sorry`, `admit`, or custom `axiom` in the Lean files
included here.
