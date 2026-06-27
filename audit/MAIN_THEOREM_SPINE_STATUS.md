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

1. `MainTheorem.positiveInsertionSubdivision_exists_of_effective_carrier`
2. `MainTheorem.exactPositiveInsertionSubdivision_exists_of_generic_effective_carrier`
3. `MainTheorem.Genericity.dense_compl_tripleBadUnion_ge_three`

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

The `n >= 3` triple-contact target has now also been reduced to a checked
finite-index statement.  The file
`Lollipop/Concrete/EndToEnd/MainTheorem/Genericity.lean` defines

```lean
MainTheorem.Genericity.OrderedTripleIndex
MainTheorem.Genericity.orderedTripleGood
MainTheorem.Genericity.compl_tripleBadUnion_eq_iInter_orderedTripleGood
MainTheorem.Genericity.dense_compl_tripleBadUnion_of_orderedTriple_open_dense
```

Thus the remaining nontrivial genericity work is no longer about unpacking
the finite union in `tripleBadUnion`; it is the analytic/geometric proof that
each fixed ordered-triple good locus is dense, with enough openness or
finite-avoidance structure to intersect the finitely many loci.

The tracked translation-avoidance route is now connected to that target.  The
main theorem genericity file proves:

```lean
MainTheorem.Genericity.translateParameterAt
MainTheorem.Genericity.continuous_translateParameterAt
MainTheorem.Genericity.exists_mem_open_not_tripleBadSet_of_pairFinite_at
MainTheorem.Genericity.pairFiniteGood
MainTheorem.Genericity.dense_orderedTripleGood_of_pairFiniteGood_dense
MainTheorem.Genericity.pairRegularGood
MainTheorem.Genericity.pairRegularGood_subset_pairFiniteGood
MainTheorem.Genericity.dense_orderedTripleGood_of_pairRegularGood_dense
MainTheorem.Genericity.circle_ne_of_center_ne
MainTheorem.Genericity.dense_pairRegularGood
MainTheorem.Genericity.dense_orderedTripleGood
MainTheorem.Genericity.dense_compl_tripleBadUnion_of_orderedTriple_open
```

The last theorem says that for one ordered triple, if the first two selected
carriers already have finite contact, then translating the third lollipop
inside any open parameter neighborhood avoids that triple-contact locus.  The
remaining global triple-density proof must still supply or construct the
finite-contact base condition in every relevant neighborhood, then iterate
this local move over all ordered triples.

The genericity `sorry` has therefore been reduced further: for each fixed
ordered triple, density of the ordered-triple good locus follows from density
of `pairFiniteGood` for the first selected pair.  The next concrete target is
to prove that fixed pair-finite locus is dense.  A still stronger checked
reduction is now available: unequal selected circles plus nonparallel selected
stems imply finite carrier contact.  Thus one viable next target is density of
`pairRegularGood i j`, the locus where those two elementary conditions hold.

That next target has now also been proved.  The file proves that
`pairRegularGood i j` is dense for every ordered distinct pair by first moving
into the nonparallel-stem locus and then translating the second center inside
that same open neighborhood.  Consequently every fixed ordered-triple good
locus is dense.

The remaining `dense_compl_tripleBadUnion_ge_three` work is now specifically
the finite simultaneous-avoidance step: either prove enough openness of the
fixed ordered-triple good loci to use the existing finite open-dense
intersection theorem, or replace that route with a sequential finite
avoidance proof that preserves previously removed triple contacts.

The sequential route now has checked append bookkeeping in
`Lollipop/Concrete/EndToEnd/TranslationGenericity.lean`:

```lean
TranslationGenericity.PairContactsFinite
TranslationGenericity.NoTripleCarrierPoints
TranslationGenericity.PairProfilesStableInBall
TranslationGenericity.pairFiniteArrangement_snoc
TranslationGenericity.noTripleCarrierPoints_snoc
TranslationGenericity.exists_norm_lt_pairFinite_noTriple_snoc_translate
TranslationGenericity.exists_norm_lt_preservePairProfiles_pairFinite_noTriple_snoc_translate
```

This proves the core one-step statement: once an old prefix has pairwise
finite contacts and no triple carrier points, a sufficiently small translation
of the next lollipop can be chosen to avoid all old double points; if old/new
pair contacts remain finite throughout the small ball, the appended prefix is
again pairwise finite and no-triple.  The remaining work for this route is the
finite induction over prefixes plus checked local neighborhoods that preserve
finite old/new contacts and the required old/new `pairExcess` values during
the translated insertion.

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

The old positive-insertion theorem-body holes in `Topology.lean` are also no
longer direct `sorry`s.  They are proved from the explicit construction
targets in
`Lollipop/Concrete/EndToEnd/MainTheorem/PositiveInsertionSubdivision.lean`:

```lean
MainTheorem.positiveInsertionSubdivision_exists_of_effective_carrier
MainTheorem.exactPositiveInsertionSubdivision_exists_of_generic_effective_carrier
```

## Removal Order

### 1. Arbitrary topology

Remove:

```lean
MainTheorem.positiveInsertionSubdivision_exists_of_effective_carrier
```

This requires the topology-first plan:

* local crosscut insertion theorem;
* carrier subdivision relative to the old-new insertion fan;
* remaining degenerate cases treated as zero-cost fan overlap pieces;
* finite localized edge filtration length bounded by fan component count.

### 2. Generic exact topology

Remove:

```lean
MainTheorem.exactPositiveInsertionSubdivision_exists_of_generic_effective_carrier
```

This uses the same subdivision as the arbitrary theorem, plus generic
two-sided splitting and exact fan counts.  The first-lollipop exact
side-realization input is already proved.

### 3. Lower genericity

Remove:

```lean
MainTheorem.Genericity.dense_compl_tripleBadUnion_ge_three
```

This is a finite algebraic avoidance theorem for triple carrier contacts in
the parameter space when `3 ≤ n`.

## Non-Drift Rule

New supporting lemmas should be added only if they directly discharge one of
the three theorem-body targets above, or a named subtarget created inside one
of those files to remove one of them.
