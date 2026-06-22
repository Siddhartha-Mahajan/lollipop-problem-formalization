# Lean formalization status

## What is present

The source tree contains the combinatorial/algebraic framework, colored Turan development, matrix compression machinery, finite carrier models, exact base-coordinate work, abstract upper/lower assembly, and concrete Euclidean lollipop modules.

`Lollipop/Concrete/EndToEnd/Final.lean` now builds a concrete endpoint

```lean
theorem Lollipop.Concrete.EndToEnd.lollipopMaximum
    (ports : Lollipop.Concrete.EndToEnd.EndToEndPorts) (n : ℕ) :
    Lollipop.Concrete.LollipopMaximumStatement n
```

This endpoint has no `GeometryCertificates` argument.  Its remaining
assumptions are explicit concrete theorem packages: `UpperPorts`, `LowerPorts`,
`GenericityAvoidance`, `PlanarTopologyPorts`, and `PairGeometryPorts`.

A comment/string-stripped static scan reports no `sorry`, `admit`, top-level `axiom`, `constant`, `opaque`, or `unsafe` declaration in the repository Lean sources. See `verification/lean_static_audit.txt`.

## Why this is not the requested end-to-end theorem

The public endpoint in `Lollipop/Final/TheoremOne.lean` requires a value of

```lean
GeometryCertificates P
```

for an abstract `MaxProblemFamily P`. Those certificates carry the model-specific upper geometry and lower blow-up realization. No concrete `MaxProblemFamily` in the project defines `region` to be the number of connected components of the complement of actual Euclidean lollipops and discharges those fields.

`Lollipop/Final/GeometryObstruction.lean` proves that a constructor of `GeometryCertificates P` for every abstract `P` is impossible. Therefore the missing step cannot be solved by filling a universally quantified certificate stub; the endpoint must be specialized to a genuine Euclidean model and the topology must be formalized.

Missing end-to-end layers are now represented by named concrete port
structures:

- `UpperPorts`: concrete upper bound for every Euclidean arrangement;
- `PlanarTopologyPorts`: arbitrary-arrangement region inequality and generic
  Euler equation;
- `PairGeometryPorts`: robust close/intriguing pair-component savings; the
  universal `2+2+2+1` pair bound is proved as
  `PairGeometry.pairExcess_le_seven`;
- `GenericityAvoidance`: density of the complement of the finite bad locus;
  points outside that locus are proved generic as
  `Lower.GenericityPort.good_is_generic`;
- blow-up chamber realization is no longer a port: canonical similarity
  transport is proved as `Lower.realizes_similarityTo_iff`, the uniform
  inter-cluster chamber radius is proved as
  `Lower.BlowUp.exists_uniform_intercluster_radius`, and realization of all
  intended blow-up pair chambers is proved as
  `Lower.BlowUp.preArrangement_realizes_concrete`;
- removing the `EndToEndPorts` argument from the final concrete theorem.

## Build status

In this integrated repository checkout, `lake build Lollipop` was run
successfully on June 22, 2026.  The build completed all 3338 jobs.

The concrete endpoint was also checked with:

```sh
lake build Lollipop.Concrete.EndToEnd
```

That build completed successfully on June 22, 2026 with 3334 jobs.

The concrete endpoint axiom print is:

```text
'Lollipop.Concrete.EndToEnd.lollipopMaximum' depends on axioms:
[propext, Classical.choice, Quot.sound]
```

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
