# Lean formalization status

## What is present

The source tree contains the combinatorial/algebraic framework, colored Turan development, matrix compression machinery, finite carrier models, exact base-coordinate work, abstract upper/lower assembly, and an algebraic module for the polynomial local family.

A comment/string-stripped static scan reports no `sorry`, `admit`, top-level `axiom`, `constant`, `opaque`, or `unsafe` declaration in the repository Lean sources. See `verification/lean_static_audit.txt`.

## Why this is not the requested end-to-end theorem

The public endpoint in `Lollipop/Final/TheoremOne.lean` requires a value of

```lean
GeometryCertificates P
```

for an abstract `MaxProblemFamily P`. Those certificates carry the model-specific upper geometry and lower blow-up realization. No concrete `MaxProblemFamily` in the project defines `region` to be the number of connected components of the complement of actual Euclidean lollipops and discharges those fields.

`Lollipop/Final/GeometryObstruction.lean` proves that a constructor of `GeometryCertificates P` for every abstract `P` is impossible. Therefore the missing step cannot be solved by filling a universally quantified certificate stub; the endpoint must be specialized to a genuine Euclidean model and the topology must be formalized.

Missing end-to-end layers include:

- concrete complement connected-component semantics;
- the arbitrary-arrangement Mayer-Vietoris/Alexander-duality region bound;
- the full close/intriguing pair-component theorems for the concrete carrier;
- chamber stability and genericization;
- similarity transport and all-size four-cluster realization;
- an unconditional final theorem for the concrete maximum.

## Build status

In this integrated repository checkout, `lake build Lollipop` was run
successfully on June 22, 2026.  The build completed all 3320 jobs.

Pinned versions:

```text
leanprover/lean4:v4.31.0-rc1
mathlib commit 859caf703c2ec80952bad6c1cd102b3f14eabf5b
```

Rebuild with:

```sh
lake build Lollipop
```

## Accurate verdict

This is a substantial conditional Lean development, not a complete certificate-free formalization of the final research manuscript.
