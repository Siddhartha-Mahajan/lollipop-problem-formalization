# Topology-First Completion Plan

Date: 2026-06-24

This is the current working plan after rereading
`manuscript/main_manuscript/main.tex` and comparing it with the concrete Lean
endpoint.  The priority is the topology proposition, not more Turan algebra,
lower-construction arithmetic, or repository reshuffling.

## Verdict

The current Lean route is valid, but it is not complete.

The manuscript proves the topology proposition by compactifying the plane,
using semialgebraic triangulation, applying Mayer-Vietoris to the compactified
carrier union, and then applying Alexander duality on `S^2`.  The Lean route
does not try to formalize that proof directly.  It replaces it with an
insertion proof:

1. insert lollipops one at a time;
2. bound the number of new complement components by the number of components
   of the compactified old-new intersection fan;
3. show that this fan count is bounded by the sum of the pair excesses
   `q(L_i,L_j)`;
4. in generic position, prove exact splitting and recover the Euler equality.

This matches the manuscript mathematically.  It proves the same two facts the
rest of the paper needs:

```lean
regionCountRat A - (n : ℚ) - 1 ≤ pairSum n (pairExcessTable A)

IsGeneric A →
  regionCountRat A = ((totalCrossingsNat A : ℕ) : ℚ) + (n : ℚ) + 1
```

The hard missing theorem is the planar local crosscut/splitting theorem.  If
that theorem cannot be proved with the available Jordan-curve bridge, the
fallback should be a finite embedded-graph face formula.  Returning to
combinatorics will not close the formalization.

## What The Manuscript Needs

The topology proposition is Proposition `top-region` in Section
`A region bound valid for arbitrary arrangements`.

For arbitrary lollipops `L_1, ..., L_n`, it states:

```text
F <= n + 1 + sum_{i<j} q(L_i,L_j)
```

where `F` is the number of connected components of the Euclidean complement,
and

```text
q(L,M) = beta_0(hat L inter hat M) - 1.
```

For generic arrangements, it states equality:

```text
F = total finite pair crossings + n + 1.
```

The manuscript uses this proposition twice:

1. Upper bound: combine it with the pair savings and the colored Turan theorem.
2. Lower bound: build a generic arrangement with the required crossing count,
   then use the generic equality to convert crossings into regions.

So an upper-only topology proof is not enough for Theorem 1.  The generic
equality case is also required.

## Definition Check

The concrete Lean definitions match the manuscript quantities.

Files:

- `Lollipop/Concrete/Basic.lean`
- `Lollipop/Concrete/EndToEnd/Compactification.lean`
- `Lollipop/Concrete/EndToEnd/Support.lean`

Key definitions:

```lean
abbrev Point : Type :=
  EuclideanSpace ℝ (Fin 2)

structure Lollipop where
  center : Point
  radial : Point
  radial_ne_zero : radial ≠ 0

def Lollipop.circle (L : Lollipop) : Set Point :=
  {x | ‖x - L.center‖ = L.radius}

def Lollipop.stem (L : Lollipop) : Set Point :=
  {x | ∃ t : ℝ, 1 ≤ t ∧ x = L.center + t • L.radial}

def Lollipop.carrier (L : Lollipop) : Set Point :=
  L.circle ∪ L.stem

def occupied (A : Arrangement n) : Set Point :=
  ⋃ i, (A i).carrier

def regionCount (A : Arrangement n) : Nat :=
  Nat.card (ConnectedComponents (FreeSpace A))
```

The one-vector lollipop model is equivalent to the manuscript's
`L(c,r,u) = C(c,r) union R(c,r,u)` with `r > 0` and unit `u`, by taking
`radial = r • u`.  This avoids a separate consistency proof that the ray
direction and radius agree.

The robust pair invariant is also the manuscript invariant:

```lean
def hatCarrier (L : Lollipop) : Set Sphere2 :=
  finiteLift L.carrier ∪ {infinity}

def hatPairIntersection (L M : Lollipop) : Set Sphere2 :=
  hatCarrier L ∩ hatCarrier M

def pairExcessNat (L M : Lollipop) : Nat :=
  componentCount (hatPairIntersection L M) - 1
```

This is exactly `q(L,M)` in the manuscript.

## Current Lean Boundary

The public concrete endpoint is still conditional:

```lean
theorem Lollipop.Concrete.EndToEnd.lollipopMaximum
    (ports : EndToEndPorts) (n : ℕ) :
    LollipopMaximumStatement n
```

The topology part of those ports has already been narrowed to:

```lean
structure InsertionFan.FanTopologyPorts : Prop where
  arbitrary_fan_bound :
    ∀ {n : ℕ} (A : Arrangement n),
      OrderedInsertionFanSplitChainBound A
  generic_exact_fan :
    ∀ {n : ℕ} {A : Arrangement n}, IsGeneric A →
      OrderedExactInsertionFanSplitChain A
```

Once this is proved as an actual theorem, Lean already constructs the older
manuscript-facing topology package:

```lean
def InsertionFan.FanTopologyPorts.toPlanarTopologyPorts :
    PlanarTopologyPorts
```

and then `Upper.lean` and `Lower.lean` consume it.

The even sharper internal target is:

```lean
structure LocalizedTopology.LocalizedFiltrationTopologyPorts : Prop where
  arbitrary_localized :
    ∀ {n : ℕ} (A : Arrangement n),
      OrderedLocalizedFiltrationBound A
  generic_exact_localized :
    ∀ {n : ℕ} {A : Arrangement n}, IsGeneric A →
      OrderedExactLocalizedFiltration A
```

This is the right implementation target because it asks for actual finite
edge filtrations of the inserted lollipop carrier.  It is not meant to remain
as a public assumption.

## Why The Insertion Route Matches Mayer-Vietoris

In the manuscript, when adding `hat L_k` to the old compactified union
`X_{k-1}`, Mayer-Vietoris gives:

```text
beta_1(X_k) <= beta_1(X_{k-1}) + beta_1(hat L_k)
               + beta_0(X_{k-1} inter hat L_k) - 1.
```

Since `hat L_k` has first Betti number one, the increase is bounded by:

```text
beta_0(X_{k-1} inter hat L_k).
```

In the Lean insertion route, this same quantity is:

```lean
componentCount (InsertionFan.insertionFan A k hk)
```

and `InsertionFan.lean` already proves:

```lean
componentCount (insertionFan A k hk) ≤
  1 + ∑ i ∈ previousIndices (⟨k, hk⟩ : Fin n),
    pairExcessNat (A i) (A ⟨k, hk⟩)
```

Thus, if one insertion raises `regionCount` by at most the fan component
count, telescoping gives the arbitrary-arrangement manuscript inequality.

In generic position, the fan consists of infinity plus the finite old-new
crossings.  Exact insertion splitting gives:

```text
region increase at step k = 1 + number of previous crossings with L_k.
```

Summing over `k` gives:

```text
F = 1 + n + total crossings.
```

That is exactly the generic equality case of Proposition `top-region`.

## Exact Work Order

Do these in order.  Do not resume lower genericity or colored Turan work until
the topology port is either proved or a fallback has been chosen.

### T1. Freeze The Theorem Targets

Create or maintain a small topology endpoint file whose final theorems have
these shapes:

```lean
theorem arbitrary_localized_topology :
    ∀ {n : ℕ} (A : Arrangement n),
      LocalizedTopology.OrderedLocalizedFiltrationBound A

theorem generic_exact_localized_topology :
    ∀ {n : ℕ} {A : Arrangement n}, IsGeneric A →
      LocalizedTopology.OrderedExactLocalizedFiltration A

def fanTopologyPorts : InsertionFan.FanTopologyPorts :=
  LocalizedTopology.fanTopologyPorts_of_localizedFiltrations
    arbitrary_localized_topology
    generic_exact_localized_topology
```

This keeps the proof aimed at the exact port currently blocking the endpoint.

### T2. Prove The Local Crosscut Theorem

This is the decisive topology theorem.

Target a new file such as:

```text
Lollipop/Concrete/EndToEnd/LocalCrosscut.lean
```

The bounded theorem should say, in effect:

```text
closed old carrier C
inserted effective edge E
simple closed curve J built from E plus an old avoiding arc
new part of E localized in one old complement component
equal Jordan side implies an avoiding simple arc in (C union E)^c
---------------------------------------------------------------
LocalizedEdgeStep C E
```

The exact theorem should add that both Jordan sides occur and produce:

```lean
LocalFiltration.LocalizedExactEdgeStep L C E
```

The proof should use only the checked small Jordan bridge:

- `JordanBridge.jordan_complement_componentCount_eq_two`
- `JordanBridge.connectedComponents_mk_eq_of_simpleArcLifting`
- `JordanBridge.exists_simpleArcEnd_disjoint_of_connectedComponents_mk_eq`

The local theorem is where the Jordan curve theorem enters.  It should not
mention Turan, pair savings, or the lower construction.

### T3. Handle The First-Lollipop/Base Insertion

The case with no old carrier must be handled explicitly.

For `k = 0`, the insertion fan is just the infinity component, so the fan
count is one.  Adding one lollipop raises the complement component count from
one to two.

The proof should use the lollipop's circle as the Jordan curve.  The outward
stem lies on the exterior side and does not create a third region.  This case
is small, but it is important because it accounts for the `+n` term in:

```text
F = crossings + n + 1.
```

### T4. Prove Carrier-Edge Subdivision

For an ordered insertion, the new compactified lollipop must be decomposed
relative to:

```lean
InsertionFan.insertionFan A k hk
```

Required output:

```text
exists m, exists f :
  InsertionFiltration.LocalizedInsertionFiltration oldPrefix newLollipop m,
  (m : ℚ) ≤ (componentCount (insertionFan A k hk) : ℚ)
```

For generic arrangements, the output must be exact:

```text
exists m, exists f :
  InsertionFiltration.LocalizedExactInsertionFiltration oldPrefix newLollipop m,
  m = componentCount (insertionFan A k hk)
```

Degenerate cases cannot be ignored.  The arbitrary upper bound must absorb:

- tangent circle intersections;
- coincident circles;
- overlapping stems;
- anchors lying in old carriers;
- fan components that are arcs rather than isolated points;
- the compactified stem endpoint at infinity.

The intended rule is: components already lying in the fan are not new edges;
the remaining effective pieces are localized insertions, and their number is
bounded by the fan component count.

### T5. Assemble Localized Filtrations

After T4, prove:

```lean
theorem arbitrary_localized_topology :
    ∀ {n : ℕ} (A : Arrangement n),
      LocalizedTopology.OrderedLocalizedFiltrationBound A

theorem generic_exact_localized_topology :
    ∀ {n : ℕ} {A : Arrangement n}, IsGeneric A →
      LocalizedTopology.OrderedExactLocalizedFiltration A
```

Then build:

```lean
def fanTopologyPorts : InsertionFan.FanTopologyPorts
```

At this point the manuscript topology proposition is formally available as:

```lean
fanTopologyPorts.toPlanarTopologyPorts.crossing_excess_le_pairSum
fanTopologyPorts.toPlanarTopologyPorts.generic_region_eq
```

### T6. Wire The Topology Theorem Into The Endpoint

Replace the topology field in `EndToEndPorts.ofFanTopology` with the actual
proved `fanTopologyPorts` theorem.  After this step, the upper bound should no
longer depend on caller-supplied topology.

The final theorem will still need lower genericity unless that has also been
proved:

```lean
Lower.GenericityPort.ChamberGenericityAvoidance n
```

### T7. Only Then Return To Lower Genericity

The remaining non-topology blocker is the generic perturbation/chamber
avoidance theorem.  It should be handled after topology because the lower
construction ultimately needs the generic topology equality anyway.

## Fallback Routes

### Route A: Current Local Crosscut Route

Use the checked Jordan bridge to prove each localized edge insertion splits
at most one old complement component, and in generic position splits it
exactly.

This is the preferred route.  It is narrower than formalizing Alexander
duality and matches the current Lean API.

### Route B: Finite Embedded-Graph Face Formula

If the local crosscut theorem becomes too hard, switch to a finite graph
theorem:

```text
for a finite tame embedded graph K in S^2,
  #pi_0(S^2 \ K) = beta_1(K) + 1.
```

Then prove that finite lollipop unions are such graphs after subdivision.
This is larger than Route A, but it is still concrete and manuscript-aligned.

### Route C: Direct Manuscript Proof

Formalize semialgebraic triangulation, Mayer-Vietoris, and Alexander duality.

This is mathematically clean but currently the least practical path.  It
would require a substantial amount of topology/algebraic-topology
infrastructure beyond the lollipop problem itself.

## Paths To Avoid

- Do not target an abstract theorem over arbitrary `MaxProblemFamily`; that
  was the old architecture mistake.
- Do not prove only the generic case; the upper bound needs arbitrary
  arrangements.
- Do not import the stale `Lollipop/Concrete/Actual/` tree wholesale.
- Do not treat Python, JSON, or rational verification scripts as trusted
  topology inputs.
- Do not add new public certificate fields for topology.  Temporary internal
  theorem targets are fine, but the endpoint should eventually construct the
  topology port itself.

## Current Bottom Line

The path is good and manuscript-valid.  The exact next mathematical problem
is:

```text
Prove the local planar crosscut theorem strongly enough to produce
localized insertion filtrations for subdivided lollipop carriers.
```

Once that is done, the existing Lean files already know how to telescope the
local statements into the manuscript topology inequality and the generic
Euler equality.
