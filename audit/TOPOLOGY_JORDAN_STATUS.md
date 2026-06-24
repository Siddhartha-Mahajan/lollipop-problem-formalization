# Topology Jordan Dependency Status

Date: 2026-06-24

This note records the current status of the local Jordan-curve dependency
after the topology-first review.

## Checked Artifacts

The local `JordanCurveTheorem/` source is now registered as a Lake library
target:

```lean
lean_lib JordanCurveTheorem where
```

The standalone Jordan statement builds:

```sh
lake build JordanCurveTheorem.JordanCurveTheoremStatement
```

The lollipop-facing bridge from Jordan side data to connected-component
cardinality also builds in the current endpoint namespace:

```sh
lake build Lollipop.Concrete.EndToEnd.JordanBridge
```

The Jordan-side classifier for localized one-edge insertions also builds:

```sh
lake build Lollipop.Concrete.EndToEnd.JordanClassifier
```

The two-arc-to-Jordan-curve helper also builds:

```sh
lake build Lollipop.Concrete.EndToEnd.ArcClosedCurve
```

The local crosscut packaging layer also builds:

```sh
lake build Lollipop.Concrete.EndToEnd.LocalCrosscut
```

The aggregate concrete endpoint builds with the Jordan bridge, classifier, and
crosscut packaging layer imported:

```sh
lake build Lollipop.Concrete.EndToEnd
```

## Axiom Audit

The two Jordan facts most relevant to the topology route have ordinary
Mathlib/foundational axiom footprints:

```text
'JordanCurveTheorem.jordan_curve_theorem' depends on axioms: [propext, Classical.choice, Quot.sound]
'JordanCurveTheorem.component_simple_arc_ver2' depends on axioms: [propext, Classical.choice, Quot.sound]
```

No `sorry`, `admit`, project `axiom`, `opaque`, or `unsafe` was found in the
checked Jordan source by the current text scan.  Comments may still contain
ordinary English words such as "constant"; those are not Lean trust hazards.

## What This Gives Us

The Jordan dependency makes the topology route more realistic.  In particular:

- `JordanCurveTheorem.jordan_curve_theorem` gives the two connected open sides
  of a simple closed curve.
- `JordanCurveTheorem.component_simple_arc_ver2` gives the useful complement
  criterion: for a closed planar set, two complement points are in the same
  connected component exactly when they can be joined by a simple arc avoiding
  the set.
- `Lollipop.Concrete.EndToEnd.JordanBridge` proves that the complement of a
  simple closed curve has exactly two connected components in the endpoint's
  `componentCount` model, and exposes avoiding-simple-arc lemmas for
  `ConnectedComponents` quotients.
- `Lollipop.Concrete.EndToEnd.JordanClassifier` turns Jordan-side equality
  plus an avoiding-arc lifting obligation into the `OneComponentSplitData` and
  `ExactOneComponentSplitData` expected by the localized insertion API.
- `Lollipop.Concrete.EndToEnd.ArcClosedCurve` proves that two simple arcs
  with the same distinct endpoints and no additional intersection form a
  simple closed curve, and therefore have a two-component complement by the
  Jordan bridge.
- `Lollipop.Concrete.EndToEnd.LocalCrosscut` packages the same data into
  `LocalizedEdgeStep`, `LocalizedExactEdgeStep`, and one-step localized
  filtrations.  It also exposes convenience constructors for the common case
  where the Jordan curve is supplied as the union of two simple arcs.

This directly supports the planned local arc-splitting theorem: form a simple
closed curve from an inserted edge plus an old avoiding arc, classify the two
new complement sides, and use simple-arc lifting to prove that at most one old
component splits.

## What It Does Not Give Yet

This does not prove the lollipop topology proposition by itself.

The larger untracked `Lollipop/Concrete/Actual/` draft tree is stale.  In
particular:

```sh
lake build Lollipop.Concrete.Actual.ComponentArcLifting
```

does not currently build.  The failure goes through older `Actual` modules
such as `Coordinates.lean` and `JordanConsequences.lean`; those modules assume
old names and an older geometry bridge.  They should not be imported into the
trusted endpoint as-is.

The useful path is now to build on the small, checked `EndToEnd` topology
bridge, two-arc closure theorem, classifier, and crosscut packaging layer:

1. prove the geometric local arc-lifting and side-surjectivity facts for a
   two-arc crosscut formed by one inserted effective edge and one old
   avoiding arc;
2. use that theorem to construct localized insertion filtrations for carrier
   subdivisions;
3. compile those filtrations through `LocalizedTopology` into
   `InsertionFan.FanTopologyPorts`.

## Current Decision

The Jordan route should remain available and should be treated as a serious
topology tool, not as an untrusted script.  It is now kernel-checked after
small API repairs.

However, the final endpoint should not import the stale `Actual` topology
tree.  The next implementation step should use
`Lollipop/Concrete/EndToEnd/JordanBridge.lean` and
`Lollipop/Concrete/EndToEnd/JordanClassifier.lean`, with
`Lollipop/Concrete/EndToEnd/ArcClosedCurve.lean` and
`Lollipop/Concrete/EndToEnd/LocalCrosscut.lean`, to prove the local
two-arc crosscut lifting theorem against the current `EndToEnd`
component-split API.
