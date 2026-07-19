# Topology-First Completion Plan

Date: 2026-06-24

This note is the current route audit after rereading
`manuscript/main_manuscript/main.tex` and comparing it with the concrete Lean
endpoint in `Lollipop/Concrete/EndToEnd/`.

The immediate instruction is to focus on topology first and plan the route
before doing more construction work.  The conclusion is:

* the current Lean route is mathematically aligned with the manuscript;
* it is not a literal formalization of the manuscript's
  Mayer-Vietoris/Alexander-duality proof;
* it targets exactly the two topology consequences used by the upper and
  lower proofs;
* the hard part is still the local planar topology theorem for inserting
  subdivided lollipop edges.

## Manuscript Dependency Check

The manuscript's topology proposition is Proposition `top-region` in
Section `A region bound valid for arbitrary arrangements`.

For arbitrary lollipops `L_1, ..., L_n`, it states

```text
F <= n + 1 + sum_{i<j} q(L_i,L_j)
```

where `F` is the number of connected components of the Euclidean complement
and

```text
q(L,M) = beta_0(hat L inter hat M) - 1.
```

For generic arrangements it also states

```text
F = total finite pair crossings + n + 1.
```

The rest of the manuscript uses exactly these two outputs:

1. Upper bound: combine the arbitrary inequality with pair savings and the
   colored Turan theorem.
2. Lower bound: build a generic arrangement with the desired crossing count,
   then use the generic equality to convert crossings into regions.

An upper-only topology formalization is therefore insufficient.  The generic
Euler equality is also required for the final theorem.

## Current Lean Boundary

The concrete model already has the right basic shape:

```lean
abbrev Point := EuclideanSpace ℝ (Fin 2)

structure Lollipop where
  center : Point
  radial : Point
  radial_ne_zero : radial ≠ 0

abbrev Arrangement (n : ℕ) := Fin n → Lollipop

def occupied (A : Arrangement n) : Set Point :=
  ⋃ i, (A i).carrier

def FreeSpace (A : Arrangement n) :=
  {x : Point // x ∉ occupied A}

noncomputable def regionCount (A : Arrangement n) : ℕ :=
  Nat.card (ConnectedComponents (FreeSpace A))
```

This one-vector model is equivalent to the manuscript's
`L(c,r,u) = C(c,r) union R(c,r,u)` with `r > 0` and unit `u`, by taking
`radial = r • u`.  It avoids storing a radius, anchor, and normalized
direction that could disagree.

The robust pair invariant also matches the manuscript:

```lean
def hatCarrier (L : Lollipop) : Set Sphere2 :=
  finiteLift L.carrier ∪ {infinity}

def hatPairIntersection (L M : Lollipop) : Set Sphere2 :=
  hatCarrier L ∩ hatCarrier M

def pairExcessNat (L M : Lollipop) : Nat :=
  componentCount (hatPairIntersection L M) - 1
```

This is the concrete Lean version of `q(L,M)`.

The public concrete endpoint is still conditional:

```lean
theorem Lollipop.Concrete.EndToEnd.lollipopMaximum
    (ports : EndToEndPorts) (n : ℕ) :
    LollipopMaximumStatement n
```

The topology part of the port has been narrowed to:

```lean
structure InsertionFan.FanTopologyPorts : Prop where
  arbitrary_fan_bound :
    ∀ {n : ℕ} (A : Arrangement n),
      OrderedInsertionFanSplitChainBound A
  generic_exact_fan :
    ∀ {n : ℕ} {A : Arrangement n}, IsGeneric A →
      OrderedExactInsertionFanSplitChain A
```

and further to the more explicit local-filtration target:

```lean
structure LocalizedTopology.LocalizedFiltrationTopologyPorts : Prop where
  arbitrary_localized :
    ∀ {n : ℕ} (A : Arrangement n),
      OrderedLocalizedFiltrationBound A
  generic_exact_localized :
    ∀ {n : ℕ} {A : Arrangement n}, IsGeneric A →
      OrderedExactLocalizedFiltration A
```

These are still theorem targets, not final public assumptions.

## Is The Current Topology Route Valid?

Yes, with one important qualification.

The manuscript proves the topology proposition by compactifying the plane,
using semialgebraic triangulation, applying Mayer-Vietoris to the compactified
carrier union, and applying Alexander duality on `S^2`.

The current Lean route replaces that proof with an insertion proof:

1. insert lollipops one at a time;
2. subdivide the new compactified lollipop carrier relative to its old-new
   intersection fan;
3. prove each effective inserted edge can split at most one old complement
   component;
4. bound the number of effective edges by the fan component count;
5. prove the fan component count is bounded by
   `1 + sum previous pairExcessNat`;
6. telescope the one-step inequalities.

This proves the same arbitrary-arrangement consequence:

```lean
regionCountRat A - (n : ℚ) - 1 ≤ pairSum n (pairExcessTable A)
```

For generic arrangements, exact local splitting plus exact fan counts prove:

```lean
regionCountRat A = ((totalCrossingsNat A : ℕ) : ℚ) + (n : ℚ) + 1
```

Those are exactly the two topology facts consumed by `Upper.lean` and
`Lower.lean`.

So the route is good if the local insertion/subdivision theorem is proved
without adding new external topology ports.  It is not good if it merely
repackages the missing topology as another certificate field.

## What Already Exists

The following checked Lean layers are relevant to the topology route:

* `PlanarInsertion.lean` telescopes local insertion inequalities into the
  global arbitrary pair-excess inequality.
* `InsertionFan.lean` proves the fan component-count budget in terms of
  previous pair excesses, and the exact generic fan count under genericity.
* `ComponentFibers.lean` proves quotient-level fibre counting for
  one-component splits.
* `ComponentSplitChain.lean` iterates one-component splits and exact splits.
* `Insertion.lean` translates split chains into region-count inequalities for
  lollipop insertion.
* `LocalizedTopology.lean` reduces the remaining topology port to finite
  localized edge filtrations.
* `JordanBridge.lean` exposes the local Jordan curve theorem and the
  avoiding-simple-arc characterization of closed-set complement components.
* `JordanClassifier.lean` turns Jordan side data plus an arc-lifting
  obligation into the active two-side classifier needed by the split API.
* `LocalCrosscut.lean` packages the Jordan classifier as localized one-edge
  filtration data.
* `ArcClosedCurve.lean` supplies the useful fact that two simple arcs with
  the same endpoints and no extra intersection form a simple closed curve.

The stale `Lollipop/Concrete/Actual/` tree should not be imported wholesale.
Some ideas can be mined from it, but the current endpoint should remain in
`Lollipop/Concrete/EndToEnd/`.

## Topology-First Work Plan

Do these before returning to lower genericity or any remaining combinatorics.

### T0. Keep The Target Fixed

The topology target is:

```lean
theorem arbitrary_localized_topology :
    ∀ {n : ℕ} (A : Arrangement n),
      LocalizedTopology.OrderedLocalizedFiltrationBound A

theorem generic_exact_localized_topology :
    ∀ {n : ℕ} {A : Arrangement n}, IsGeneric A →
      LocalizedTopology.OrderedExactLocalizedFiltration A
```

Then:

```lean
def fanTopologyPorts : InsertionFan.FanTopologyPorts :=
  LocalizedTopology.fanTopologyPorts_of_localizedFiltrations
    arbitrary_localized_topology
    generic_exact_localized_topology
```

Do not weaken this to a new caller-supplied topology certificate.

### T1. Prove The Local Crosscut Theorem

This is the first real topology theorem to prove.

Mathematical statement:

* `C` is the old closed carrier.
* `E` is one effective inserted edge.
* `E \ C` lies in one old complement component.
* A simple closed curve `J` is formed by `E` plus an old avoiding arc.
* Equal Jordan side implies an avoiding simple arc in `(C ∪ E)ᶜ`.
* In the generic/exact case, both Jordan sides occur.

Lean output:

```lean
LocalFiltration.LocalizedEdgeStep C E
LocalFiltration.LocalizedExactEdgeStep L C E
```

Current supporting files:

```text
Lollipop/Concrete/EndToEnd/JordanBridge.lean
Lollipop/Concrete/EndToEnd/JordanClassifier.lean
Lollipop/Concrete/EndToEnd/LocalCrosscut.lean
Lollipop/Concrete/EndToEnd/ArcClosedCurve.lean
```

The real missing obligation is the arc-lifting statement: two descendants of
the active old component that lie on the same Jordan side must be joined by a
simple arc avoiding the enlarged carrier.

### T2. Prove The First-Lollipop/Base Insertion

The insertion proof must account for the `+n` term.  The first lollipop is
not a normal old-new fan step.

Required result:

```text
adding one isolated lollipop to the empty arrangement changes the complement
component count from 1 to 2.
```

Use the lollipop circle as the Jordan curve.  The outward stem lies in the
exterior side and does not create a third component.

This case should produce the one-step localized filtration data needed by the
global induction.

### T3. Prove Carrier Subdivision Relative To The Fan

For an ordered insertion of `A k`, subdivide the compactified new lollipop
carrier relative to:

```lean
InsertionFan.insertionFan A k hk
```

Required arbitrary output:

```lean
∃ m : ℕ,
∃ f : InsertionFiltration.LocalizedInsertionFiltration
    (PlanarInsertion.prefixArrangement A k (Nat.le_of_lt hk))
    (A ⟨k, hk⟩) m,
  (m : ℚ) ≤
    (componentCount (InsertionFan.insertionFan A k hk) : ℚ)
```

Required generic output:

```lean
∃ m : ℕ,
∃ f : InsertionFiltration.LocalizedExactInsertionFiltration
    (PlanarInsertion.prefixArrangement A k (Nat.le_of_lt hk))
    (A ⟨k, hk⟩) m,
  m = componentCount (InsertionFan.insertionFan A k hk)
```

Degenerate cases cannot be ignored for the arbitrary upper bound:

* tangent circle intersections;
* coincident circles;
* overlapping stems;
* anchors lying in old carriers;
* intersection fans that contain arcs instead of isolated points;
* the stem endpoint at infinity after compactification.

The intended rule is that fan components are already old-new overlap, while
the complementary effective pieces of the new lollipop carrier are the
localized edge insertions.  The number of effective pieces must be bounded by
the fan component count.

### T4. Assemble Localized Filtrations

After T3, prove:

```lean
theorem arbitrary_localized_topology :
    ∀ {n : ℕ} (A : Arrangement n),
      LocalizedTopology.OrderedLocalizedFiltrationBound A

theorem generic_exact_localized_topology :
    ∀ {n : ℕ} {A : Arrangement n}, IsGeneric A →
      LocalizedTopology.OrderedExactLocalizedFiltration A
```

Then use:

```lean
LocalizedTopology.fanTopologyPorts_of_localizedFiltrations
```

At this point the manuscript topology proposition is available to the rest of
the endpoint through:

```lean
fanTopologyPorts.toPlanarTopologyPorts.crossing_excess_le_pairSum
fanTopologyPorts.toPlanarTopologyPorts.generic_region_eq
```

### T5. Remove Topology From The Endpoint Ports

Replace the topology field in:

```lean
EndToEndPorts.ofFanTopology
UpperPorts
LowerPorts
```

with the actual proved `fanTopologyPorts`.

After this, the upper bound should no longer require caller-supplied
topology.

### T6. Return To Lower Genericity

Only after topology is closed, finish the remaining lower-construction
genericity theorem:

```lean
∀ n : ℕ, Lower.GenericityPort.ChamberGenericityAvoidance n
```

This is needed because the lower construction uses the generic topology
equality.  It is secondary to topology, but still required before the final
endpoint is unconditional.

### T7. Remove The Final Ports Argument

Once topology and lower genericity are theorems, define the final endpoint:

```lean
theorem lollipopMaximum (n : ℕ) :
    LollipopMaximumStatement n
```

or the expanded form:

```lean
theorem lollipopMaximum_expanded (n : ℕ) :
    IsGreatest
      (Set.range (fun A : Arrangement n => (regionCount A : ℚ)))
      (4 * ((n.choose 2 : ℕ) : ℚ) +
        TheoremOneManuscript.manuscriptS n + (n : ℚ) + 1)
```

Then run:

```lean
#print axioms Lollipop.Concrete.EndToEnd.lollipopMaximum
```

The expected result should contain only ordinary Lean/Mathlib foundations
such as `propext`, `Classical.choice`, and `Quot.sound`.

## Decision Points And Fallbacks

### Preferred Route A: Local Crosscut Insertion

Use the checked Jordan bridge to prove that each localized effective edge
splits at most one old complement component, and exactly one in generic
position.

This is the best current route because it is narrower than formalizing
Alexander duality and already matches the Lean API.

Continue Route A if:

* the arc-lifting theorem can be stated without hidden assumptions;
* carrier subdivision gives finitely many localized edge steps;
* degenerate fan components can be treated as zero-cost overlap pieces.

### Fallback Route B: Finite Embedded-Graph Face Formula

If local crosscut insertion fails, prove a finite embedded graph theorem:

```text
for a finite tame embedded graph K in S^2,
  #pi_0(S^2 \ K) = beta_1(K) + 1.
```

Then prove finite lollipop unions become such embedded graphs after
subdivision.

This is still manuscript-aligned but larger than Route A.

Switch to Route B if:

* same-side arc lifting cannot be obtained without essentially proving a
  global graph-face theorem anyway;
* overlapping/tangent degeneracies make local edge insertion too case-heavy;
* the subdivision bookkeeping becomes less work than the local complement
  topology.

### Fallback Route C: Direct Manuscript Topology

Formalize semialgebraic triangulation, Mayer-Vietoris, and Alexander duality.

This is mathematically clean but currently the least practical route.  It
would require substantial algebraic-topology and semialgebraic infrastructure
beyond the lollipop theorem itself.

Only switch to Route C if the project goal becomes formalizing the manuscript
proof literally rather than proving the same theorem efficiently in Lean.

## Paths To Avoid

* Do not target an abstract theorem over arbitrary `MaxProblemFamily`.
* Do not introduce new public `GeometryCertificates` or topology-certificate
  fields.
* Do not prove only the generic case; the upper bound needs arbitrary
  arrangements.
* Do not import `Lollipop/Concrete/Actual/` wholesale.
* Do not use Python/JSON verification scripts as trusted theorem inputs.
* Do not continue lower-genericity or matrix work while the topology port is
  still open.

## Remaining Work After Topology

After `fanTopologyPorts` is proved, the remaining final-formalization work is
smaller and more algebraic:

1. Prove the all-`n` reduced lower genericity avoidance theorem, currently
   represented by
   `Lower.GenericityPort.ChamberGenericityAvoidance n`.
2. Wire the proved topology and genericity theorems into `LowerPorts` and
   `UpperPorts`.
3. Remove `EndToEndPorts` from the final concrete theorem.
4. Run `lake build Lollipop.Concrete.EndToEnd` and `lake build Lollipop`.
5. Run the trust audit:

   ```sh
   rg -n "\bsorry\b|\badmit\b|\baxiom\b|\bopaque\b|\bunsafe\b|\bnative_decide\b" \
     Lollipop/Concrete Lollipop/Internal Lollipop/Final Lollipop.lean
   ```

6. Record the final `#print axioms` output in `README.md`.

## Bottom Line

The current topology route is good and valid for the manuscript theorem, but
it remains the critical path.  The next mathematical deliverable is not more
colored Turan work and not more lower arithmetic.  It is:

```text
prove the local planar crosscut theorem and use it to build localized
insertion filtrations for subdivided lollipop carriers.
```

Once that is done, the existing Lean reduction files already know how to
telescope the local topology into the manuscript's arbitrary region
inequality and generic Euler equality.
