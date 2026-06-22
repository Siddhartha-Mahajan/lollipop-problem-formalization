# Concrete End-To-End Import Status

Date: 2026-06-22

Source archive:
`lollipop-problem-formalization-main`

## What Was Copied

The concrete end-to-end bundle listed in
`audit/concrete_end_to_end_added_files.txt` was copied into this repository.
The archive also contained a full duplicate of the surrounding repository; those
duplicate existing files were not recopied except where the concrete coordinate
and topology bridge needed local porting fixes.

Ignored archive noise:

* `.DS_Store` files

## Porting Fixes Made

* Replaced the stale one-point compactification import with
  `Mathlib.Topology.Compactification.OnePoint.Basic`.
* Moved `unitRadial` and `stemByDistance` API to the concrete `Lollipop`
  namespace so dot notation works on `Lollipop.Concrete.Lollipop`.
* Replaced the unavailable `Real.arctan2` proof with a `Complex.arg` proof for
  normalized bearings.
* Repaired coordinate-to-`EuclideanSpace` bridge proofs using the existing
  `SphereBridge` API.
* Made the finite-point/one-point compactification coercion conversion explicit
  in `freeSpaceEquivHatComplement`.
* Repaired the shared `Support` file through the purely mechanical API issues:
  convexity of stems, compactness of compactified carriers, finite unions of
  compact carriers, the finite-lift-plus-infinity component count, the current
  `PairwiseDisjoint` API, and connectedness of unions with a common point.

## Commands Run

```text
lake build Lollipop.Concrete.EndToEnd.Coordinate
```

Result: succeeded.

```text
lake build Lollipop.Concrete.EndToEnd.Compactification
```

Result: succeeded.

```text
lake build Lollipop.Concrete.EndToEnd
```

Result: failed in `Lollipop/Concrete/EndToEnd/Support.lean`.

The remaining failure is not a syntax issue. After the local porting fixes,
`Support.lean` now stops exactly at the substantial topology and
Euclidean-geometry facts that are not yet proved in this repository:

* `component_excess_union_infinity_le_one`
* `finite_circle_intersection_of_ne`
* `circle_intersection_ncard_le_two`
* `finite_circle_ray_intersection`
* `circle_ray_intersection_ncard_le_two`
* `component_excess_of_convex_finite_chart_le_one`
* `isolated_zero_of_regular_level_pair_circle_equations`
* `isolated_zero_of_regular_ray_circle_equation`
* `isolated_intersection_of_nonparallel_affine_lines`

```text
lake build Lollipop
```

Result: succeeded.

## Current Interpretation

The imported concrete bundle is useful as an architectural scaffold and now has
buildable coordinate and compactification layers. It is not a kernel-checked
end-to-end proof. The remaining failures are exactly in the intended hard
support layer: finite primitive-intersection geometry, component-excess
topology, and later planar/Alexander-duality-style machinery.
