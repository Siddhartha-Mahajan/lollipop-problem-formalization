# Concrete end-to-end Lean development

This directory contains the original lollipop formalization plus a new concrete
end-to-end development under `Lollipop.Concrete.EndToEnd`.

## Public entry point

Use either

```lean
import Lollipop.Concrete.EndToEnd
```

or the standalone root module

```lean
import LollipopConcreteEndToEnd
```

The intended endpoint is

```lean
Lollipop.Concrete.EndToEnd.lollipopMaximum
  (n : ℕ) : Lollipop.Concrete.LollipopMaximumStatement n
```

The expanded endpoint is

```lean
Lollipop.Concrete.EndToEnd.lollipopMaximum_expanded
```

It is stated directly for concrete Euclidean lollipops and the connected
components of their complement.  It has no `GeometryCertificates` parameter.

## Added modules

The concrete proof chain is split into the following files.

* `Coordinate.lean`: coordinate conversion and normalized bearings derived from
  the concrete center/radial-vector model.
* `Compactification.lean`: one-point compactification, compactified carriers,
  and the robust pair-excess invariant.
* `Support.lean`: primitive circle/ray intersections and shared finite-component
  geometry.
* `PlanarTopology.lean`: the arbitrary-arrangement region inequality and the
  exact generic Euler formula.
* `PairGeometry.lean`: universal, close, intriguing, and combined pair-excess
  bounds.
* `Upper.lean`: construction of the data consumed by the existing colored
  Turán/Paulsen combinatorial backend and the concrete upper bound.
* `Lower/Similarity.lean`: transport of local constructions by positive plane
  similarities.
* `Lower/PairChamber.lean`: strict polynomial pair chambers and exact primitive
  crossing counts.
* `Lower/RationalBase.lean`: exact rational four-lollipop base arrangement.
* `Lower/PolynomialFamily.lean`: corrected local polynomial family with four
  crossings between distinct nearby members.
* `Lower/Genericity.lean`: semialgebraic avoidance inside open pair chambers.
* `Lower/BlowUp.lean`: four-cluster construction and conversion to the existing
  lower-bound algebra.
* `Lower.lean`: all-size concrete lower theorem.
* `Final.lean`: combination of upper and lower bounds into `IsGreatest`.
* `Lollipop/Concrete/EndToEnd.lean` and `LollipopConcreteEndToEnd.lean`: import
  facades.

## Last corrections merged into this archive

1. The intriguing-circle relation now matches the manuscript exactly:
   disjoint circles are intriguing, as are meeting circles with
   `d² ≤ r₁² + r₂²`; an external tangency is not intriguing.
2. The five-circle/Paulsen obstruction is applied to one common, slightly
   enlarged auxiliary radius system.  Pair-component estimates remain about
   the original lollipops.
3. The zero-lollipop topology branches use `regionCount_zero A`, so they work
   for the actual empty arrangement argument rather than a mismatched closed
   theorem.
4. `Lollipop` receives the topology induced by its center/radial coordinates,
   making pair chambers and perturbation statements live on the intended
   parameter space.
5. The false ray-ray strict chamber now excludes parallelism; parallel stems
   are treated as a boundary degeneracy rather than an open chamber.
6. Pair-code swapping was made direct and nonrecursive, with explicit symmetry
   of the circle margins.
7. Pair-code specifications require swapping only off the diagonal, which is
   exactly where pair codes are used.
8. Blow-up code symmetry now carries `i ≠ j` and uses distinct local parameters
   inside a cluster, removing the spurious equal-parameter branch.

## Verification status

No Lean or Lake command was run while producing this bundle.  The new source
contains no `sorry`, `admit`, or newly declared `axiom`, but it is not a
kernel-verified completion.  The namespaces named `TopologyPort`,
`EuclideanPort`, `PairPort`, `UpperPort`, `PairChamberPort`, `GenericityPort`,
and `BlowUpPort` isolate the substantial topology, primitive-intersection,
semialgebraic, and version-sensitive Mathlib API work.  Their theorem bodies
spell out the intended proof route and calls, but names and interfaces may need
to be implemented or adapted when compiled against the pinned toolchain.

See `audit/concrete_end_to_end_static_check.txt` and
`audit/concrete_end_to_end_sha256.txt` for the packaging audit.

## Integration status in this repository

On 2026-06-22, after importing the bundle here:

* `lake build Lollipop.Concrete.EndToEnd.Coordinate` succeeded.
* `lake build Lollipop.Concrete.EndToEnd.Compactification` succeeded.
* `lake build Lollipop.Concrete.EndToEnd` failed in
  `Lollipop/Concrete/EndToEnd/Support.lean` because the file refers to
  substantial topology and Euclidean-geometry support names that are not present
  in the pinned project.
* `lake build Lollipop` still succeeded.

See `audit/concrete_end_to_end_integration_status_2026_06_22.md`.
