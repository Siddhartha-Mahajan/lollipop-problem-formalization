# Lollipop Formula Formalization

This repository contains the current manuscript, the Lean development, and
the audit record for the lollipop formula project.

## Start Here

- Manuscript: `manuscript/main_manuscript/main.tex`
- Rendered PDF: `manuscript/main_manuscript/main.pdf`
- Lean public endpoint: `Lollipop/Final/TheoremOne.lean`
- Audit verdict: `audit/AUDIT_AND_VERDICT.md`
- Lean status note: `audit/FORMALIZATION_STATUS.md`

## Manuscript

The current manuscript is the publishable source in:

```text
manuscript/main_manuscript/
```

Render it with:

```sh
cd manuscript/main_manuscript
tectonic main.tex
```

The old manuscript copies have been removed from the handoff path.

## Lean Status

The main public theorem endpoint is conditional on geometric certificates:

```lean
theorem Lollipop.Final.theorem_one
    (P : TheoremOne.MaxProblemFamily)
    (h : Lollipop.Final.GeometryCertificates P) :
    Lollipop.Final.TheoremOneStatement P
```

Lean proves the theorem assembly from those certificates, including the
finite carrier algebra, colored Turan reduction, matrix/compression
arguments, lower-bound summation, and formula bridge.

This repository is not claiming a certificate-free formalization of actual
Euclidean complement connected components.  The precise boundary is recorded
in `audit/FORMALIZATION_STATUS.md`.

Build the Lean project with:

```sh
lake build Lollipop
```

## Geometry And Lower Construction

The research-grade Lean tree includes the polynomial local blow-up family:

```text
Lollipop/Internal/Manuscript/PrimitiveGeometry/PolynomialBlowUp.lean
```

The public geometry-facing files remain:

```text
Lollipop/Final/Geometry.lean
Lollipop/Final/GeometryObstruction.lean
Lollipop/Final/TheoremOne.lean
```

`GeometryObstruction.lean` records why `GeometryCertificates P` cannot be
constructed uniformly for every abstract `MaxProblemFamily`; a concrete
Euclidean model still has to supply the genuine geometry/topology semantics.

## Audit Folder

`audit/` contains the separate audit material:

```text
audit/AUDIT_AND_VERDICT.md
audit/CHANGELOG.md
audit/FORMALIZATION_STATUS.md
audit/proof_audit_checklist.md
audit/theorem_dependency_map.md
audit/verification/
audit/scripts/
```

The verification scripts can be run from the repository root:

```sh
python3 audit/scripts/certify_rational_base.py
python3 audit/scripts/verify_blowup.py
python3 audit/scripts/verify_combinatorics.py
python3 audit/scripts/audit_lean.py
```

Python dependencies for the verification scripts are listed in
`audit/requirements.txt`.

## Repository Layout

```text
Lollipop.lean
Lollipop/
expected_fail/
manuscript/main_manuscript/
audit/
references/
lakefile.lean
lake-manifest.json
lean-toolchain
```

## Build Notes

After integrating the research-grade tree on June 22, 2026,
`lake build Lollipop` completed successfully with 3320 jobs.  With the
existing local `.lake/` cache, that build took 9.45 seconds after the one
local proof-script repair in `PolynomialBlowUp.lean`.

On this machine, the first fresh build of the earlier standalone repository
from an empty `.lake/` cache took about 25 minutes, including cloning and
compiling mathlib dependencies.  After the local `.lake/` cache existed, a
no-op `lake build Lollipop` took 3.83 seconds.
