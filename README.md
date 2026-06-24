# Lollipop Formula Formalization

This repository contains the current manuscript, the Lean development, and
the audit record for the lollipop formula project.

## Start Here

- Manuscript: `manuscript/main_manuscript/main.tex`
- Rendered PDF: `manuscript/main_manuscript/main.pdf`
- Lean public endpoint: `Lollipop/Final/TheoremOne.lean`
- Concrete endpoint: `Lollipop/Concrete/EndToEnd/Final.lean`
- Audit verdict: `audit/AUDIT_AND_VERDICT.md`
- Lean status note: `audit/FORMALIZATION_STATUS.md`
- Concrete final-target note:
  `audit/UNCONDITIONAL_FORMALIZATION_VERDICT.md`

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

The intended complete endpoint is not `theorem_one` with better abstract
certificates.  It is a concrete Euclidean theorem, with lollipops,
complements, connected-component region counts, and the maximum statement
defined directly in Lean.  The current target note is
`audit/UNCONDITIONAL_FORMALIZATION_VERDICT.md`.

The concrete Lean endpoint now lives in `Lollipop/Concrete/EndToEnd/Final.lean`.
It states the final theorem directly for Euclidean lollipops and
connected-component region counts:

```lean
theorem Lollipop.Concrete.EndToEnd.lollipopMaximum
    (ports : Lollipop.Concrete.EndToEnd.EndToEndPorts) (n : ℕ) :
    Lollipop.Concrete.LollipopMaximumStatement n
```

This is not yet an unconditional theorem: `EndToEndPorts` explicitly packages
the remaining concrete theorem targets.  The current port boundary is:

- `UpperPorts`: upper-bound inputs that still need geometry/topology:
  currently only `PlanarTopologyPorts`.  The pair-excess bounds, four-direction
  close forcing, five-circle forcing for the concrete `Intriguing` relation,
  and colored-Turan reduction are proved in Lean by `PairGeometry.lean` and
  `regionCountRat_le_candidate`.
- `LowerPorts`: lower construction from genericity and the planar topology
  generic Euler equation.
- The blow-up chamber-realization layer is now proved in Lean.  Canonical
  similarity transport is `Lower.realizes_similarityTo_iff`, the uniform
  inter-cluster chamber radius is `Lower.BlowUp.exists_uniform_intercluster_radius`,
  and the constructed pre-arrangements realize the intended pair chambers by
  `Lower.BlowUp.preArrangement_realizes_concrete`.
- `ChamberGenericityAvoidance`: density of the complement of the reduced
  strict-chamber bad locus.  Once a strict pair chamber is fixed, Lean now
  proves pair finiteness, primitive transversality, and anchor avoidance from
  the chamber itself via `Lower.GenericityPort.good_is_generic_in_pair_chamber`.
  Parallel-stem density is now proved for all `n` by
  `Lower.GenericityPort.dense_compl_parallelBadUnion`, so the reduced
  lower-genericity handoff is down to the triple-contact open/dense facts,
  packaged by
  `Lower.GenericityPort.chamberGenericityAvoidance_of_triple_open_dense`.
  The cases `n = 0, 1, 2` are proved outright.
  The older stronger `GenericityAvoidance` route remains available, with
  `GenericityAvoidancePieces.toGenericityAvoidance` decomposing the full bad
  locus; the parallel-stem open/dense theorems and the `n = 0, 1`
  full-avoidance proofs are still recorded there.
- `PlanarTopologyPorts`: arbitrary-arrangement region inequality and generic
  Euler equation.  The `n = 0` instances of component finiteness, the upper
  inequality, and the generic Euler equation are proved in
  `Lollipop/Concrete/EndToEnd/PlanarTopology.lean`.  The quotient-level
  component-fibre bookkeeping for one-component insertions is now proved in
  `Lollipop/Concrete/EndToEnd/ComponentFibers.lean`; finite split chains and
  their translation back to actual `regionCount` insertion bounds are proved
  in `ComponentSplitChain.lean` and `Insertion.lean`.  The ordered-prefix
  reduction in `PlanarInsertion.lean` proves that local insertion bounds, or
  stronger split-chain data with the right edge budget, imply the global
  arbitrary-arrangement pair-excess inequality; `PlanarTopology.lean` exposes
  constructors from those local inputs to `PlanarTopologyPorts`.
- Pair geometry is no longer a port.  The universal `2+2+2+1` pair bound,
  close-pair saving, intriguing-pair saving, combined close/intriguing saving,
  and Paulsen inflated five-circle forcing are proved in
  `Lollipop/Concrete/EndToEnd/PairGeometry.lean`.

Build the Lean project with:

```sh
lake build Lollipop
```

## Lean Verification Checklist

The Lean community checklist is saved at
`references/lean_verification/did_you_prove_it.md`.  Current answers for this
repository:

- Repository: yes.  This is a Lake project with `lean-toolchain`,
  `lakefile.lean`, and `lake-manifest.json`.
- Build: yes for the imported handoff tree.  `lake build Lollipop` completed
  successfully on June 23, 2026.
- Main proof checked by the build: yes.  `Lollipop.lean` imports
  `Lollipop.Final`, which imports `Lollipop/Final/TheoremOne.lean`.
- Standard axioms only: yes for the checked theorem bodies.  After
  `lake build Lollipop.Final` on June 23, 2026, the exact output was:

  ```text
  'Lollipop.Final.theorem_one' depends on axioms: [propext, Classical.choice, Quot.sound]
  ```

  The finite star-forest canonical-shape classifier used by the theorem was
  replaced by explicit structural Lean proofs for support sizes zero through
  five, so no project `native_decide` axiom remains in this theorem's axiom
  list.
- Does it prove the claimed theorem: conditionally.  Lean proves the final
  formula from `GeometryCertificates P`; it does not yet construct those
  certificates for the actual Euclidean lollipop model without remaining
  geometric assumptions.
- Concrete endpoint: conditionally, but with no `GeometryCertificates`.
  `lake build Lollipop.Concrete.EndToEnd` completed successfully on
  June 23, 2026 with 3334 jobs.  The exact axiom check for the concrete
  endpoint was:

  ```text
  'Lollipop.Concrete.EndToEnd.lollipopMaximum' depends on axioms: [propext, Classical.choice, Quot.sound]
  ```

  The concrete endpoint now runs the existing colored-Turán backend without
  adding any nonstandard proof axiom.

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
constructed uniformly for every abstract `MaxProblemFamily`; the concrete
endpoint now avoids that abstraction, but still exposes the remaining
geometry/topology as concrete theorem packages.

## Audit Folder

`audit/` contains the separate audit material:

```text
audit/AUDIT_AND_VERDICT.md
audit/CHANGELOG.md
audit/FORMALIZATION_STATUS.md
audit/UNCONDITIONAL_FORMALIZATION_VERDICT.md
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
`lake build Lollipop` completed successfully with 3338 jobs.  On June 23, 2026,
the same full target was rerun successfully with 3338 jobs.  With the
existing local `.lake/` cache, that build took 9.45 seconds after the one
local proof-script repair in `PolynomialBlowUp.lean`.

On this machine, the first fresh build of the earlier standalone repository
from an empty `.lake/` cache took about 25 minutes, including cloning and
compiling mathlib dependencies.  After the local `.lake/` cache existed, a
no-op `lake build Lollipop` took 3.83 seconds.

The concrete endpoint build `lake build Lollipop.Concrete.EndToEnd` completed
successfully on June 24, 2026 with 3340 jobs after proving the all-`n`
parallel-stem density theorem for the reduced chamber-genericity port.
