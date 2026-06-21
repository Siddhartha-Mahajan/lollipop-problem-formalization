# Lollipop End-to-End Formalization

This repository is the cleaned Lean handoff for the lollipop manuscript.
It has one public theorem endpoint and one explicit remaining geometry
boundary.

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
Lollipop.Final.theorem_one
Lollipop.Final.displayed_formula
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
carrier-counting, lower-bound summation, and theorem-assembly parts after the
geometric certificate boundary is supplied.

The single public certificate boundary is:

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
```

It intentionally fails at exactly these names:

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

Run it with:

```sh
lake env lean expected_fail/MissingGeometryCertificates.lean
```

The expected result is two unknown-identifier errors at the names above.

## Repository Layout

```text
Lollipop.lean
Lollipop/Final.lean
Lollipop/Final/TheoremOne.lean
Lollipop/Final/Geometry.lean
Lollipop/Internal/
expected_fail/MissingGeometryCertificates.lean
manuscript/
references/
lakefile.lean
lake-manifest.json
lean-toolchain
```

`Lollipop/Final/` is the public surface.  `Lollipop/Internal/` is the proof
closure required by the final endpoint; it is not a collection of competing
final theorem statements.

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
