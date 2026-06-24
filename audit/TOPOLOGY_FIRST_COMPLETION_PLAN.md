# Topology-First Completion Plan

Date: 2026-06-24

This note zooms out from the current implementation and fixes the next route.
The immediate priority is the topology proposition from the manuscript, not
more lower-construction or combinatorial work.

## Executive Decision

The current Lean path is valid if, and only if, we prove the remaining
`FanTopologyPorts` theorem package.

The manuscript proves the topology step by semialgebraic triangulation,
Mayer-Vietoris, and Alexander duality on `S^2`.  The current Lean development
does not try to reproduce that machinery directly.  Instead, it reduces the
same topology result to a constructive insertion theorem: add lollipops one at
a time, split each new compactified lollipop at its contacts with the old
carrier, and prove that each resulting arc raises the complement component
count by at most one.  In generic position, each such arc raises the count by
exactly one.

This is a good route because it proves the exact facts needed by the
manuscript:

```lean
regionCountRat A - (n : Rat) - 1 <= pairSum n (pairExcessTable A)
```

and, for generic arrangements,

```lean
regionCountRat A = ((totalCrossingsNat A : Nat) : Rat) + (n : Rat) + 1
```

It is not yet a proof.  The hard gate is the local planar arc-splitting
theorem.  If that gate cannot be proved with elementary plane topology, the
fallback must be a finite embedded-graph/Jordan-curve theorem, not more
algebra or more Turan work.

## What the Manuscript Needs

The topology proposition in `manuscript/main_manuscript/main.tex` states:

1. For arbitrary lollipops `L_1, ..., L_n`, if `F` is the number of
   complementary connected components, then

   ```text
   F <= n + 1 + sum_{i<j} q(L_i,L_j).
   ```

   Here `q(L,M)` is the number of connected components of
   `hat L inter hat M`, minus the shared component containing infinity.

2. For generic arrangements, equality holds and `q(L_i,L_j)` is the ordinary
   number of finite pairwise crossings.

The rest of the manuscript uses this in two places:

1. Upper bound: combine the topology inequality with the pair savings and the
   colored Turan theorem.
2. Lower bound: construct generic arrangements with the required number of
   finite crossings, then use the generic topology equality to convert
   crossings into regions.

Therefore a complete formalization cannot be finished until the topology
proposition is proved inside Lean for the concrete lollipop model.

## Manuscript Cross-Check

The current topology-first route is aligned with the manuscript, but it is
not the same proof.

The manuscript proves Proposition `top-region` by:

1. compactifying the plane to `S^2`;
2. using semialgebraic triangulation to make every lollipop union and
   intersection a finite compact subcomplex;
3. applying Mayer-Vietoris to bound `beta_1` of the compactified carrier
   union;
4. applying Alexander duality to convert `beta_1` into complement-component
   count;
5. using finite graph Euler counting in the generic equality case.

The Lean route should not silently assume any of those facts.  It replaces
steps 2--4 by a constructive insertion proof.  This is valid only if it proves
the same three formal consequences:

```lean
Finite (ConnectedComponents (FreeSpace A))
regionCountRat A - (n : Rat) - 1 <= pairSum n (pairExcessTable A)
IsGeneric A -> regionCountRat A =
  ((totalCrossingsNat A : Nat) : Rat) + (n : Rat) + 1
```

The definitions already match the manuscript's intended quantities:

- `hatCarrier L` is the compactified lollipop carrier `L ∪ {∞}`;
- `hatPairIntersection L M` is `hatCarrier L ∩ hatCarrier M`;
- `pairExcessNat L M = componentCount (hatPairIntersection L M) - 1`,
  matching `q(L,M) = beta_0(hat L ∩ hat M) - 1`;
- `regionCount A` is the cardinality of connected components of the actual
  Euclidean complement.

So the route is conceptually sound.  The remaining question is not whether the
target is the right theorem; it is whether the local planar separation theorem
can be proved in the current Mathlib environment without importing a large
Jordan-curve/Alexander-duality development.

## Current Lean Boundary

The concrete final theorem is currently conditional:

```lean
theorem Lollipop.Concrete.EndToEnd.lollipopMaximum
    (ports : Lollipop.Concrete.EndToEnd.EndToEndPorts) (n : Nat) :
    Lollipop.Concrete.LollipopMaximumStatement n
```

The topology boundary has already been narrowed.  The older port is
`PlanarTopologyPorts`:

```lean
structure PlanarTopologyPorts : Prop where
  region_components_finite :
    forall {n : Nat} (A : Arrangement n),
      Finite (ConnectedComponents (FreeSpace A))
  crossing_excess_le_pairSum :
    forall {n : Nat} (A : Arrangement n),
      regionCountRat A - (n : Rat) - 1 <=
        Lollipop.pairSum n (pairExcessTable A)
  generic_region_eq :
    forall {n : Nat} {A : Arrangement n}, IsGeneric A ->
      regionCountRat A =
        ((totalCrossingsNat A : Nat) : Rat) + (n : Rat) + 1
```

The sharper current target is `InsertionFan.FanTopologyPorts`:

```lean
structure FanTopologyPorts : Prop where
  arbitrary_fan_bound :
    forall {n : Nat} (A : Arrangement n),
      OrderedInsertionFanSplitChainBound A
  generic_exact_fan :
    forall {n : Nat} {A : Arrangement n}, IsGeneric A ->
      OrderedExactInsertionFanSplitChain A
```

Once `FanTopologyPorts` is proved, Lean already constructs
`PlanarTopologyPorts`, and then the existing upper/lower theorem assembly can
consume it.

The still sharper working target is now the localized-filtration package in
`Lollipop/Concrete/EndToEnd/LocalizedTopology.lean`:

```lean
structure LocalizedFiltrationTopologyPorts : Prop where
  arbitrary_localized :
    forall {n : Nat} (A : Arrangement n), OrderedLocalizedFiltrationBound A
  generic_exact_localized :
    forall {n : Nat} {A : Arrangement n}, IsGeneric A ->
      OrderedExactLocalizedFiltration A
```

This is not intended as a new public certificate boundary.  It is an internal
reduction target: construct actual localized edge filtrations, then Lean
already compiles them to `FanTopologyPorts`.

Files already doing useful checked work:

- `Lollipop/Concrete/EndToEnd/ComponentFibers.lean`: quotient-level component
  cardinality for one-component splits.
- `Lollipop/Concrete/EndToEnd/ComponentSplitChain.lean`: finite chains of
  those one-component splits.
- `Lollipop/Concrete/EndToEnd/Insertion.lean`: translates split chains into
  actual `regionCount` inequalities.
- `Lollipop/Concrete/EndToEnd/PlanarInsertion.lean`: turns ordered insertion
  inequalities into the global pair-sum topology inequality.
- `Lollipop/Concrete/EndToEnd/InsertionFan.lean`: proves fan component
  budgets and reduces the remaining topology to `FanTopologyPorts`.
- `Lollipop/Concrete/EndToEnd/ComponentLifting.lean`,
  `ComponentSurjectivity.lean`, `OccupiedTopology.lean`, `LocalInsertion.lean`,
  `LocalFiltration.lean`, `InsertionFiltration.lean`, and
  `LocalizedTopology.lean`: reduce the local topology obligation to producing
  localized insertion filtrations edge-by-edge.

Untracked Jordan/topology drafts in the working tree are references only.
They are not part of the checked endpoint until they build cleanly and are
imported by the main Lake target.

## Topology-First Work Order

This is the concrete order from here.  Do not return to Turan, matrix, or
lower-genericity work until either this route succeeds or a fallback is chosen.

1. Verify the definitions-to-manuscript bridge.

   Confirm in Lean that `pairExcessNat` is exactly the manuscript `q`, that
   the insertion fan is `hatCarrier new ∩ hatOccupied old`, and that the
   ordered insertion sums telescope to the manuscript pair sum.

2. Prove the local planar arc theorem.

   First target a clean model: a closed embedded segment inside an open disk
   or rectangle, with endpoints on the old carrier and interior in one old
   complement component.  Prove deleting it raises the number of complement
   components by at most one, and in the two-sided/generic case by exactly
   one.  This is the decisive gate.

3. Transport the local theorem to lollipop carrier edges.

   A subdivided circle arc or stem arc must be reduced to the local model by
   an explicit homeomorphism or by direct parametrization.  The proof must
   cover finite stem pieces and the compactified stem edge ending at infinity.

4. Build the carrier subdivision.

   For each ordered insertion, split the new compactified carrier along the
   fan `hatCarrier new ∩ hatOccupied old`.  Degenerate overlaps must be
   absorbed into the fan so that the remaining effective pieces are localized
   edges with interiors disjoint from the old carrier.

5. Assemble localized filtrations.

   Produce `OrderedLocalizedFiltrationBound A` for arbitrary arrangements and
   `OrderedExactLocalizedFiltration A` under `IsGeneric A`.  Then use
   `LocalizedFiltrationTopologyPorts.toFanTopologyPorts` to obtain
   `FanTopologyPorts`.

6. Remove the topology port from the final endpoint.

   Once `FanTopologyPorts` is an actual theorem rather than a parameter, wire
   it through `EndToEndPorts.ofFanTopology`.  At that point the upper bound
   no longer depends on caller-supplied topology.

7. Only then return to lower genericity.

   The remaining non-topology gate is
   `forall n, Lower.GenericityPort.ChamberGenericityAvoidance n`, currently
   reduced mostly to triple-contact open/dense facts.

## Failure Gates

Route A should be abandoned only for a specific reason:

- If the local segment theorem cannot be proved without a Jordan-style
  separation result, switch to Route B and formalize the finite embedded-graph
  face formula.
- If lollipop edge subdivision cannot handle arbitrary degeneracies, keep the
  generic exact route but prove the arbitrary upper bound through the finite
  embedded-graph/Mayer-Vietoris inequality.
- If Mathlib has usable homology/Alexander-duality APIs that make the
  manuscript proof shorter than the insertion route, switch to Route C.

Do not add more ports, theorem aliases, or external scripts to bypass these
gates.  Any successful route must end in ordinary Lean theorems feeding
`PlanarTopologyPorts`.

## Route A: Preferred Insertion-Split Proof

This route proves the manuscript topology proposition without formalizing
Alexander duality.

### A1. Freeze the topology interface

Do not broaden `EndToEndPorts`.  Do not add new certificate fields.  The target
is exactly:

```lean
theorem fanTopologyPorts :
    Lollipop.Concrete.EndToEnd.InsertionFan.FanTopologyPorts
```

and then a no-port final theorem of the form:

```lean
theorem lollipopMaximum_unconditional (n : Nat) :
    Lollipop.Concrete.LollipopMaximumStatement n
```

after the remaining lower genericity port is also proved.

### A2. Prove the local arc-split theorem

Create a small topology module, for example:

```text
Lollipop/Concrete/EndToEnd/Topology/ArcSplit.lean
```

Target theorem shape:

```lean
theorem oneComponentSplit_of_embedded_arc
    {K e : Set Point} :
    ArcInsertionHypotheses K e ->
    ComponentFibers.OneComponentSplitData
      (Insertion.union_compl_subset_occupied_compl_for_sets K e)
```

and the exact version:

```lean
theorem exactOneComponentSplit_of_crossing_arc
    {K e : Set Point} :
    ExactArcInsertionHypotheses K e ->
    ComponentFibers.ExactOneComponentSplitData
      (Insertion.union_compl_subset_occupied_compl_for_sets K e)
```

The proof obligation is topological:

- all old complement components except the one containing the arc are
  unchanged;
- the active old component has at most two new components after deleting the
  arc;
- in the exact generic case, both sides of the arc are nonempty and remain
  separated.

This is the first critical gate.  It may require a specialized Jordan arc
separation lemma.  The narrowest useful statement is not the full Jordan curve
theorem, but separation by one embedded arc inside a disk or inside a known
old complement component.

### A3. Define compactified lollipop edge decompositions

Create:

```text
Lollipop/Concrete/EndToEnd/Topology/CarrierSubdivision.lean
```

Use the existing objects:

- `Sphere2`
- `hatCarrier`
- `hatPairIntersection`
- `InsertionFan.pairIntersectionFan`
- `pairExcessNat`

For one insertion into a prefix arrangement, define the fan:

```lean
pairIntersectionFan (previousIndices k) (fun i => A i) (A k)
```

Then split the new compactified lollipop carrier along this fan.  Each
remaining edge should be an embedded arc whose interior is disjoint from the
old occupied carrier.

Degenerate cases must be handled by putting the whole overlap into the fan:

- coincident circle pieces;
- overlapping stems;
- tangencies;
- anchor contacts;
- contacts connected through infinity.

The budget needed for the arbitrary upper bound is only an inequality:

```text
number of effective inserted arcs <= componentCount(insertion fan)
```

The existing `InsertionFan` file already proves the fan count is bounded by
`1 + sum previous pairExcessNat`; the missing part is constructing the split
chain from actual carrier arcs.

### A4. Prove arbitrary fan-bound split chains

Target:

```lean
theorem arbitrary_fan_bound :
    forall {n : Nat} (A : Arrangement n),
      PlanarInsertion.OrderedInsertionFanSplitChainBound A
```

For each prefix insertion:

1. build the fan;
2. subdivide the new carrier by the fan;
3. order the resulting effective arcs;
4. apply the local arc-split theorem to each arc;
5. assemble the result with `ComponentSplitChain`.

This proves:

```lean
regionCountRat A - (n : Rat) - 1 <= pairSum n (pairExcessTable A)
```

through already checked reductions.

### A5. Prove generic exact fan chains

Target:

```lean
theorem generic_exact_fan :
    forall {n : Nat} {A : Arrangement n}, IsGeneric A ->
      PlanarInsertion.OrderedExactInsertionFanSplitChain A
```

In a generic arrangement:

- pair intersections are finite points;
- there are no triple points;
- no finite crossing lies at an anchor;
- stems are nonparallel and nonoverlapping;
- each old/new contact is isolated;
- each inserted edge contributes exactly one split.

The existing `InsertionFan` counting lemmas already show that the fan count is
`1 + previousPairAdded`.  What remains is the exact topological separation
for every inserted edge.

### A6. Assemble topology

After A4 and A5:

```lean
def fanTopologyPorts : InsertionFan.FanTopologyPorts where
  arbitrary_fan_bound := arbitrary_fan_bound
  generic_exact_fan := generic_exact_fan
```

Then:

```lean
def planarTopologyPorts : PlanarTopologyPorts :=
  fanTopologyPorts.toPlanarTopologyPorts
```

At that point the upper bound has its topology input, and the lower bound has
the generic Euler equation it needs.

## Route B: Fallback Finite Embedded-Graph Proof

If A2 cannot be proved without a hidden full Jordan theorem, switch to a
finite embedded-graph theorem.

Target statement:

```text
For a finite tame graph K embedded in S^2,
number of components of S^2 \ K = 1 + beta_1(K).
```

Then instantiate `K` with the compactified lollipop carrier union after
subdivision at all pair intersections and anchors.

This route is closer to the manuscript's generic graph counting and arbitrary
Betti-number bound, but it requires more infrastructure:

- a finite graph model for compactified lollipop unions;
- subdivision of circles and rays into graph edges;
- Euler characteristic or graph homology;
- a planar face formula or Jordan-curve theorem for finite embedded graphs.

This is more work than Route A, but it is mathematically robust.

## Route C: Fallback Homology/Alexander-Duality Proof

This follows the manuscript most literally:

1. one-point compactify the plane;
2. prove compactified lollipop unions are finite semialgebraic subcomplexes;
3. use Mayer-Vietoris to prove the `beta_1` inequality;
4. use Alexander duality on `S^2`;
5. prove the generic graph equality by Euler characteristic.

This route is valid mathematically, but it is probably the longest Lean route
because Mathlib does not currently make this exact Alexander-duality argument
available as a ready theorem.

Use this only if the specialized insertion and embedded-graph routes both
fail.

## What Not To Work On Yet

Until `FanTopologyPorts` is proved or rejected, do not spend main effort on:

- further colored Turan work;
- more matrix compression proofs;
- new aliases of Theorem 1;
- polishing the README;
- untrusted Jordan imports;
- lower genericity beyond small reusable lemmas already needed by topology.

Those are not the current bottleneck.

## Exact Milestones From Here

### T0. Clean and verify the baseline

Run:

```sh
lake build Lollipop.Concrete.EndToEnd
```

Record the current imported state and keep untracked drafts out of the trusted
chain unless deliberately imported and built.

Exit criterion: the current conditional concrete endpoint still builds.

### T1. State the local arc-split API

Add only definitions and theorem statements needed for `OneComponentSplitData`
and `ExactOneComponentSplitData`.

Exit criterion: the API typechecks and does not mention lollipops yet.

### T2. Prove local arc-split for the simplest model

First prove the theorem for a straight closed segment in an open rectangle or
disk, with endpoints on the boundary and interior in the old complement.

Exit criterion: Lean proves a concrete two-side classifier into `Fin 2` and
uses it to construct `OneComponentSplitData`.

Decision gate: if this already requires a general Jordan curve theorem, stop
Route A and switch to Route B.

### T3. Transport local arc-split to lollipop edge arcs

Prove that every carrier edge obtained by subdivision is homeomorphic, locally
or globally, to the straight-segment model.

Exit criterion: each inserted lollipop edge supplies the split data required
by `ComponentSplitChain`.

### T4. Build arbitrary insertion chains

Use fan subdivisions for every prefix insertion.

Exit criterion:

```lean
theorem arbitrary_fan_bound :
    forall {n : Nat} (A : Arrangement n),
      OrderedInsertionFanSplitChainBound A
```

### T5. Build generic exact insertion chains

Use `IsGeneric A` to show each inserted edge exactly splits one active
component.

Exit criterion:

```lean
theorem generic_exact_fan :
    forall {n : Nat} {A : Arrangement n}, IsGeneric A ->
      OrderedExactInsertionFanSplitChain A
```

### T6. Remove the topology port

Define:

```lean
def fanTopologyPorts : InsertionFan.FanTopologyPorts
```

and verify:

```sh
lake build Lollipop.Concrete.EndToEnd
```

Exit criterion: `UpperPorts` and `LowerPorts` can obtain topology without a
caller-supplied field.

### T7. Return to lower genericity

Only after topology is closed, finish:

```lean
forall n : Nat, Lower.GenericityPort.ChamberGenericityAvoidance n
```

The parallel-stem density piece is already proved.  The remaining work is the
triple-contact open/dense theorem.

### T8. Assemble the no-port final theorem

Final target:

```lean
theorem lollipopMaximum_unconditional (n : Nat) :
    Lollipop.Concrete.LollipopMaximumStatement n
```

Then run:

```sh
lake build Lollipop
#print axioms Lollipop.Concrete.EndToEnd.lollipopMaximum_unconditional
```

Exit criterion:

- no `EndToEndPorts` argument;
- no `GeometryCertificates` argument;
- no `sorry`, `admit`, project `axiom`, `constant`, `opaque`, or `unsafe`;
- axiom output only contains ordinary Mathlib/foundational axioms such as
  `propext`, `Classical.choice`, and `Quot.sound`.

## Current Assessment

The path is good, but the project should now stop circling around the lower
and combinatorial layers.  The decisive theorem is topology.

The insertion-split route is aligned with the manuscript because it proves the
same arbitrary-region inequality and the same generic Euler equality.  It is
also narrower than proving Alexander duality in Lean.  Its risk is that the
local statement "an embedded arc splits at most one planar complement
component, and exactly one in the generic case" may still require substantial
Jordan-style topology.

If the local arc-split theorem is proved, the rest of the topology route is
mostly finite bookkeeping and subdivision.  If it fails, the correct fallback
is a finite embedded-graph theorem for lollipop carrier unions, not another
certificate abstraction.
