# Main Theorem Spine Status

Date: 2026-06-27

This is the current audit after switching to the main-theorem-first workflow.
The theorem spine now has a single import target:

```text
Lollipop/Concrete/EndToEnd/MainTheorem.lean
```

The final endpoint is visible in:

```text
Lollipop/Concrete/EndToEnd/MainTheorem/Assembly.lean
```

The main theorem path is split into:

```text
Lollipop/Concrete/EndToEnd/MainTheorem/PositiveInsertionSubdivision.lean
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

or, equivalently, with the aggregate import:

```sh
lake build Lollipop.Concrete.EndToEnd.MainTheorem
```

Lean reports the current intended `sorry`s below.

## Current Intended `sorry` Targets

1. `MainTheorem.effectiveLocalizedCarrierSubdivisionData_exists`

Everything else in `MainTheorem.Assembly` is ordinary wiring from that named
target into the existing concrete upper and lower endpoint.

## What Has Been Narrowed

The previous broad genericity placeholder
`chamberGenericityAvoidance_all` is no longer a `sorry`.

It is now assembled from checked Lean proofs of:

* the nonparallel-stem bad-locus complement is open dense;
* triple contacts are impossible for `n < 3`;
* `dense_compl_tripleBadUnion_ge_three`, proved by a sequential finite
  prefix-genericization argument;
* the chamber-bad complement is the intersection of the nonparallel and
  no-triple complements.

The `n >= 3` triple-contact target was closed without assuming openness of
every fixed triple-good locus.  The file
`Lollipop/Concrete/EndToEnd/MainTheorem/Genericity.lean` defines

```lean
MainTheorem.Genericity.OrderedTripleIndex
MainTheorem.Genericity.orderedTripleGood
MainTheorem.Genericity.compl_tripleBadUnion_eq_iInter_orderedTripleGood
MainTheorem.Genericity.dense_compl_tripleBadUnion_of_orderedTriple_open_dense
```

Those fixed-triple reductions are still present as useful checked facts, but
the final proof now uses an insertion-order construction instead of relying on
finite intersections of open dense triple-good sets.

The checked genericity route proves:

```lean
MainTheorem.Genericity.translateParameterAt
MainTheorem.Genericity.continuous_translateParameterAt
MainTheorem.Genericity.exists_mem_open_not_tripleBadSet_of_pairFinite_at
MainTheorem.Genericity.pairFiniteGood
MainTheorem.Genericity.dense_orderedTripleGood_of_pairFiniteGood_dense
MainTheorem.Genericity.pairRegularGood
MainTheorem.Genericity.pairRegularGood_subset_pairFiniteGood
MainTheorem.Genericity.pairCenterRegularGood
MainTheorem.Genericity.isOpen_pairCenterRegularGood
MainTheorem.Genericity.dense_pairCenterRegularGood
MainTheorem.Genericity.allPairCenterRegularGood
MainTheorem.Genericity.isOpen_allPairCenterRegularGood
MainTheorem.Genericity.dense_allPairCenterRegularGood
MainTheorem.Genericity.pairFiniteArrangement_of_mem_allPairCenterRegularGood
MainTheorem.Genericity.exists_norm_ball_translateParameterAt_subset_open_allPairCenterRegularGood
MainTheorem.Genericity.dense_orderedTripleGood_of_pairRegularGood_dense
MainTheorem.Genericity.circle_ne_of_center_ne
MainTheorem.Genericity.dense_pairRegularGood
MainTheorem.Genericity.dense_orderedTripleGood
MainTheorem.Genericity.dense_compl_tripleBadUnion_of_orderedTriple_open
MainTheorem.Genericity.not_mem_tripleBadUnion_iff_noTripleCarrierPoints
MainTheorem.Genericity.not_mem_tripleBadUnion_of_noTripleCarrierPoints
MainTheorem.Genericity.pairContactsFinite_prefix_translate_of_mem_allPairCenterRegularGood
MainTheorem.Genericity.prefix_translateParameterAt_succ_eq_snoc
MainTheorem.Genericity.exists_translateParameterAt_step_prefix_noTriple
MainTheorem.Genericity.exists_mem_open_allPairCenterRegularGood_prefix_noTriple
MainTheorem.Genericity.exists_mem_open_allPairCenterRegularGood_noTriple
MainTheorem.Genericity.dense_compl_tripleBadUnion_ge_three
MainTheorem.Genericity.dense_compl_tripleBadUnion
MainTheorem.Genericity.dense_compl_chamberBadUnion
MainTheorem.Genericity.chamberGenericityAvoidance_all
```

The sequential proof starts from the checked open dense all-pairs regular
locus:

```lean
MainTheorem.Genericity.allPairCenterRegularGood
MainTheorem.Genericity.dense_allPairCenterRegularGood
MainTheorem.Genericity.pairFiniteArrangement_of_mem_allPairCenterRegularGood
MainTheorem.Genericity.exists_norm_ball_translateParameterAt_subset_open_allPairCenterRegularGood
```

Membership in this locus gives distinct centers and nonparallel stems for
every ordered pair, hence the concrete `TranslationGenericity.PairFiniteArrangement`
invariant needed before the first triple-removing insertion step.  The small
translation neighborhood theorem proves that translating one selected center
can be kept inside any prescribed open subset of this all-pairs locus.
The triple-bad-union bridge identifies the terminal no-triple invariant from
the insertion-order construction with the actual target complement of
`Lower.GenericityPort.tripleBadUnion`.

The append bookkeeping lives in
`Lollipop/Concrete/EndToEnd/TranslationGenericity.lean`:

```lean
TranslationGenericity.PairContactsFinite
TranslationGenericity.NoTripleCarrierPoints
TranslationGenericity.PairProfilesStableInBall
TranslationGenericity.pairFiniteArrangement_empty
TranslationGenericity.noTripleCarrierPoints_empty
TranslationGenericity.pairFiniteArrangement_prefix
TranslationGenericity.noTripleCarrierPoints_prefix
TranslationGenericity.pairFiniteArrangement_snoc
TranslationGenericity.noTripleCarrierPoints_snoc
TranslationGenericity.exists_norm_lt_pairFinite_noTriple_snoc_translate
TranslationGenericity.exists_norm_lt_preservePairProfiles_pairFinite_noTriple_snoc_translate
```

Together these now prove the genericity side of the main theorem spine.  No
genericity theorem-body `sorry` remains in `MainTheorem/Genericity.lean`.

The previous broad topology placeholders are also no longer direct
`intro; sorry` proofs.  They now assemble from first-insertion and
positive-insertion filtration targets:

* first-lollipop side arc-lifting;
* arbitrary bounded localized filtration for effective non-first insertions;
* exact localized filtration for non-first generic insertions.

The full-overlap arbitrary insertion case is now proved:

```lean
MainTheorem.positiveInsertionSubdivision_of_carrier_subset_old
```

Consequently `MainTheorem.positiveInsertionSubdivision_exists` is now
ordinary case-splitting between the proved zero-edge full-overlap case and
the remaining effective-carrier subdivision theorem.

For generic exact insertions, the full-overlap case is impossible:

```lean
MainTheorem.not_carrier_subset_old_of_isGeneric
```

The disjoint whole-carrier one-edge case is also reduced to the local
Jordan-crosscut side-lifting input:

```lean
MainTheorem.insertionFan_eq_singleton_infinity_of_carrier_subset_prefix_compl
MainTheorem.componentCount_insertionFan_eq_one_of_carrier_subset_prefix_compl
MainTheorem.positiveInsertionSubdivision_of_disjoint_carrier_jordanCrosscut
MainTheorem.exactPositiveInsertionSubdivision_of_disjoint_carrier_jordanCrosscut
MainTheorem.positiveInsertionSubdivision_exists_of_disjoint_carrier_crosscut
MainTheorem.exactPositiveInsertionSubdivision_exists_of_disjoint_carrier_crosscut
```

The local topology bridge now also supports subdivision edges whose endpoints
or overlap pieces lie on the old carrier.  The key new lemma is:

```lean
MainTheorem.edgeLocalized_of_isConnected_newPart
```

and the matching Jordan/two-arc constructors are:

```lean
MainTheorem.localizedEdgeStepOfConnectedNewPartJordanCrosscut
MainTheorem.localizedExactEdgeStepOfConnectedNewPartJordanCrosscut
MainTheorem.localizedEdgeStepOfConnectedNewPartTwoArcCrosscut
MainTheorem.localizedExactEdgeStepOfConnectedNewPartTwoArcCrosscut
```

This is the form needed for the real carrier-subdivision theorem: effective
subdivision arcs may have endpoints on the old carrier, but their genuinely
new part must lie in one old complement component.

The one-piece effective-carrier subcase now has bounded and exact
constructors:

```lean
MainTheorem.positiveInsertionSubdivision_of_connectedNewPart_carrier_jordanCrosscut
MainTheorem.exactPositiveInsertionSubdivision_of_connectedNewPart_carrier_jordanCrosscut
```

These handle insertions where the whole genuinely new carrier part is
connected.  The remaining full theorem must cut the carrier at all old-new
fan components and apply the same connected-new-part constructor to each
effective piece.

The effective-carrier hypothesis itself has also been unpacked into a checked
new-point lemma and one-piece `Nonempty` reductions:

```lean
MainTheorem.exists_new_point_of_effective_carrier
MainTheorem.positiveInsertionSubdivision_exists_of_effective_connectedNewPart_crosscut
MainTheorem.exactPositiveInsertionSubdivision_exists_of_effective_connectedNewPart_crosscut
```

So the one-piece branch now has the following exact remaining input: build a
Jordan crosscut around a genuinely new carrier point, prove same-side
arc-lifting in the enlarged complement, and in the exact case prove both
Jordan sides are realized.

The localized filtration API now has concatenation operations:

```lean
LocalFiltration.LocalizedEdgeFiltration.append
LocalFiltration.LocalizedExactEdgeFiltration.append
```

These are the bookkeeping operations needed after the carrier is cut into
multiple connected-new-part pieces.

The exact localized-filtration API can also now forget exactness:

```lean
LocalFiltration.LocalizedExactEdgeFiltration.toLocalizedEdgeFiltration
MainTheorem.ExactPositiveInsertionSubdivision.toPositive
```

This keeps the bounded upper-bound insertion theorem downstream of the exact
generic construction whenever exact subdivision data is available, while the
arbitrary effective-carrier theorem still needs its own non-generic proof.

The insertion-fan budget for the first insertion is proved:

```lean
MainTheorem.Topology.componentCount_insertionFan_zero
```

The whole first-insertion filtration is now ordinary constructor wiring from
the two first-lollipop edge-step targets.

The two first-lollipop edge-step targets are now ordinary constructor wiring
from the active classifier.  The classifier injectivity and surjectivity
theorems are also wiring from sharper first-lollipop topology targets.

The first-lollipop side-realization theorem is now proved:

```lean
MainTheorem.Topology.firstLollipopActiveSideSurjective
```

It follows from the existing component-map surjectivity theorem applied to
the inclusion of the full lollipop complement into the circle complement.

The first-lollipop side arc-lifting theorem performs the Lean-obvious
reduction from equal Jordan side to equal circle-complement component.  It
also proves the interior case: if both points lie inside the metric circle,
the straight segment between them stays inside the open disk and is disjoint
from the full lollipop carrier.

The exterior stem-slit theorem is now proved.  It first reduces by the
existing positive-similarity infrastructure to the standard unit lollipop, and
the standard case connects arbitrary exterior points to a common far
upper-left point by vertical and horizontal segments that avoid the unit
circle and positive real stem.

The old positive-insertion theorem-body holes in `Topology.lean` are not
direct `sorry`s.  They are proved from the explicit construction targets in
`Lollipop/Concrete/EndToEnd/MainTheorem/PositiveInsertionSubdivision.lean`:

```lean
MainTheorem.positiveInsertionSubdivision_exists_of_effective_carrier
MainTheorem.exactPositiveInsertionSubdivision_exists_of_generic_effective_carrier
```

Those two endpoint targets are now ordinary consequences of the single
remaining effective-carrier subdivision package:

```lean
MainTheorem.EffectiveLocalizedCarrierSubdivisionData
MainTheorem.effectiveLocalizedCarrierSubdivisionData_exists
MainTheorem.EffectiveCarrierSubdivisionData
MainTheorem.effectiveCarrierSubdivisionData_exists
```

`EffectiveLocalizedCarrierSubdivisionData` is the constructive target.  It
contains the actual bounded localized edge filtration and, under `IsGeneric A`,
an exact localized edge filtration whose length is definitionally the insertion
fan component count.  `EffectiveCarrierSubdivisionData` is now just the
compiled subdivision object obtained from those localized filtrations.  Neither
structure is a public certificate argument.

The one-piece connected-new-part case now has a checked constructor:

```lean
MainTheorem.effectiveLocalizedCarrierSubdivisionData_of_disjoint_carrier_crosscut
MainTheorem.effectiveLocalizedCarrierSubdivisionData_exists_of_disjoint_carrier_crosscut
MainTheorem.effectiveLocalizedCarrierSubdivisionData_of_connectedNewPart_crosscut
MainTheorem.effectiveLocalizedCarrierSubdivisionData_exists_of_effective_connectedNewPart_crosscut
```

The first two handle the no-overlap branch where the inserted carrier avoids
the old prefix carrier; the insertion fan is `{∞}` and the whole carrier is a
single localized edge.  The latter two handle the one-piece overlap branch.
Thus any future proof that the effective inserted carrier has one connected
new part, one fan component, and a realized Jordan crosscut immediately
produces the localized data required by the main topology target.

## Removal Order

### 1. Effective carrier subdivision

Remove:

```lean
MainTheorem.effectiveLocalizedCarrierSubdivisionData_exists
```

This requires the topology-first plan:

* local crosscut insertion theorem;
* carrier subdivision relative to the old-new insertion fan;
* remaining degenerate cases treated as zero-cost fan overlap pieces;
* finite localized edge filtration length bounded by fan component count.
* generic two-sided splitting and exact fan counts for the exact field.

## Non-Drift Rule

New supporting lemmas should be added only if they directly discharge the
theorem-body target above, or a named subtarget created inside
`PositiveInsertionSubdivision.lean` to remove it.
