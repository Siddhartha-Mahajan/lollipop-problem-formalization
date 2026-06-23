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
`ChamberGenericityAvoidance`, and `PlanarTopologyPorts`.

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

- `UpperPorts`: upper-bound inputs still needed by the concrete colored-Turan
  assembly: currently only `PlanarTopologyPorts`.  The four-direction close
  forcing and colored-Turan reduction are proved in
  `Lollipop/Concrete/EndToEnd/Upper.lean`, while the pair-excess savings and
  five-circle forcing for the concrete `Intriguing` relation are proved in
  `Lollipop/Concrete/EndToEnd/PairGeometry.lean`;
- `PlanarTopologyPorts`: arbitrary-arrangement region inequality and generic
  Euler equation.  The `n = 0` instances of component finiteness, the
  arbitrary upper inequality, and the generic Euler equation are proved in
  `Lollipop/Concrete/EndToEnd/PlanarTopology.lean`;
- Pair geometry is no longer a port: the universal `2+2+2+1` pair bound,
  close-pair saving, intriguing-pair saving, combined close/intriguing saving,
  and Paulsen inflated five-circle forcing are proved in
  `Lollipop/Concrete/EndToEnd/PairGeometry.lean`;
- `ChamberGenericityAvoidance`: density of the complement of the reduced
  strict-chamber bad locus.  Once a strict pair chamber is fixed, Lean proves
  pair finiteness, primitive transversality, and anchor avoidance from that
  chamber as `Lower.GenericityPort.good_is_generic_in_pair_chamber`, so the
  lower construction now only asks genericity to avoid triple contacts and
  parallel stems.  This reduced theorem is assembled from triple and parallel
  pieces by
  `Lower.GenericityPort.ChamberGenericityAvoidancePieces.toChamberGenericityAvoidance`.
  The older stronger `GenericityAvoidance` route remains available and is
  reduced by
  `Lower.GenericityPort.GenericityAvoidancePieces.toGenericityAvoidance` to
  open/dense complement obligations for the named pair, anchor, triple, and
  parallel bad-locus unions; the open-complement part for the parallel-stem
  union is proved as `Lower.GenericityPort.isOpen_compl_parallelBadUnion`,
  and full-locus avoidance is proved outright for arrangements of size zero
  and one;
- blow-up chamber realization is no longer a port: canonical similarity
  transport is proved as `Lower.realizes_similarityTo_iff`, the uniform
  inter-cluster chamber radius is proved as
  `Lower.BlowUp.exists_uniform_intercluster_radius`, and realization of all
  intended blow-up pair chambers is proved as
  `Lower.BlowUp.preArrangement_realizes_concrete`;
- removing the `EndToEndPorts` argument from the final concrete theorem.

## Build status

In this integrated repository checkout, `lake build Lollipop` was run
successfully on June 23, 2026.  The build completed all 3338 jobs.

The concrete endpoint was also checked with:

```sh
lake build Lollipop.Concrete.EndToEnd
```

That build completed successfully on June 23, 2026 with 3335 jobs.

The concrete endpoint axiom print is:

```text
'Lollipop.Concrete.EndToEnd.lollipopMaximum' depends on axioms: [propext, Classical.choice, Quot.sound]
```

The concrete endpoint has no project `native_decide` axiom in its transitive
axiom list.  The finite star-forest canonical-shape classifier used by the
colored-Turan backend was replaced by explicit structural Lean proofs for
support sizes zero through five on June 23, 2026.

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
