# Main Theorem Spine Status

Date: 2026-06-24

This is the current audit after switching to the main-theorem-first workflow.
The final endpoint is now visible in:

```text
Lollipop/Concrete/EndToEnd/MainTheorem/Assembly.lean
```

The main theorem path is split into:

```text
Lollipop/Concrete/EndToEnd/MainTheorem/Topology.lean
Lollipop/Concrete/EndToEnd/MainTheorem/Genericity.lean
Lollipop/Concrete/EndToEnd/MainTheorem/Upper.lean
Lollipop/Concrete/EndToEnd/MainTheorem/Lower.lean
Lollipop/Concrete/EndToEnd/MainTheorem/Assembly.lean
```

The assembly theorem has no caller-supplied `EndToEndPorts` argument.  Its
remaining trust gap is exactly the named `sorry` list below.

## Current Build Gate

The theorem spine builds with:

```sh
lake build Lollipop.Concrete.EndToEnd.MainTheorem.Assembly
```

Lean reports the current intended `sorry`s below.

## Current Intended `sorry` Targets

1. `MainTheorem.Topology.firstLollipopActiveSideArcLifting`
2. `MainTheorem.Topology.firstLollipopActiveSideSurjective`
3. `MainTheorem.Topology.localizedInsertionFiltration_bound_positive`
4. `MainTheorem.Topology.localizedExactInsertionFiltration_of_generic_positive`
5. `MainTheorem.Genericity.dense_compl_tripleBadUnion_ge_three`

Everything else in `MainTheorem.Assembly` is ordinary wiring from those named
targets into the existing concrete upper and lower endpoint.

## What Has Been Narrowed

The previous broad genericity placeholder
`chamberGenericityAvoidance_all` is no longer a `sorry`.

It is now assembled from:

* the existing proof that the nonparallel-stem locus is open dense;
* the new proof that triple contacts are impossible for `n < 3`;
* the remaining theorem
  `dense_compl_tripleBadUnion_ge_three`.

The previous broad topology placeholders are also no longer direct
`intro; sorry` proofs.  They now assemble from first-insertion and
positive-insertion filtration targets:

* first-lollipop side arc-lifting;
* first-lollipop side realization;
* arbitrary bounded localized filtration for non-first insertions;
* exact localized filtration for non-first generic insertions.

The insertion-fan budget for the first insertion is proved:

```lean
MainTheorem.Topology.componentCount_insertionFan_zero
```

The whole first-insertion filtration is now ordinary constructor wiring from
the two first-lollipop edge-step targets.

The two first-lollipop edge-step targets are now ordinary constructor wiring
from the active classifier.  The classifier injectivity and surjectivity
theorems are also wiring from the two sharper first-lollipop topology targets
listed above.

## Removal Order

### 1. Arbitrary topology

Remove:

```lean
MainTheorem.Topology.firstLollipopActiveSideArcLifting
MainTheorem.Topology.localizedInsertionFiltration_bound_positive
```

This requires the topology-first plan:

* local crosscut insertion theorem;
* carrier subdivision relative to the old-new insertion fan;
* degenerate cases treated as zero-cost fan overlap pieces;
* finite localized edge filtration length bounded by fan component count.

### 2. Generic exact topology

Remove:

```lean
MainTheorem.Topology.firstLollipopActiveSideSurjective
MainTheorem.Topology.localizedExactInsertionFiltration_of_generic_positive
```

This uses the same subdivision as the arbitrary theorem, plus generic
two-sided splitting and exact fan counts.

### 3. Lower genericity

Remove:

```lean
MainTheorem.Genericity.dense_compl_tripleBadUnion_ge_three
```

This is a finite algebraic avoidance theorem for triple carrier contacts in
the parameter space when `3 ≤ n`.

## Non-Drift Rule

New supporting lemmas should be added only if they directly discharge one of
the three targets above, or a named subtarget created inside one of those
files to remove one of them.
