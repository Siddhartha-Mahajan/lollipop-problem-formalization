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

The lollipop-facing adapter from Jordan side data to connected-component
cardinality also builds:

```sh
lake build Lollipop.Concrete.Actual.JordanAdapter
```

The existing concrete endpoint still builds and does not yet import this
Jordan dependency:

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
- `Lollipop.Concrete.Actual.JordanAdapter` proves that the complement of a
  simple closed curve has exactly two connected components in the project's
  `ConnectedComponents` model.

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

The useful path is to port only the small, checked pieces into a clean
`EndToEnd` topology bridge:

1. import the checked Jordan theorem source;
2. recreate the small component-cardinality adapter in the `EndToEnd`
   namespace;
3. prove the local arc-split theorem for one inserted edge;
4. use that theorem to construct localized insertion filtrations;
5. compile those filtrations through `LocalizedTopology` into
   `InsertionFan.FanTopologyPorts`.

## Current Decision

The Jordan route should remain available and should be treated as a serious
topology tool, not as an untrusted script.  It is now kernel-checked after
small API repairs.

However, the final endpoint should not import the stale `Actual` topology
tree.  The next implementation step should be a fresh, minimal
`Lollipop/Concrete/EndToEnd/Topology/JordanBridge.lean` or equivalent module
that depends only on the checked Jordan theorem and the current `EndToEnd`
component-split API.
