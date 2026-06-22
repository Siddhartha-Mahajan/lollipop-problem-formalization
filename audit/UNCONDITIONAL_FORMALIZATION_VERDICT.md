# Unconditional Formalization Verdict

Saved from a user-supplied planning note on June 22, 2026.

## Repository action taken

After adding this note, this repository was updated in the direction it
recommends:

* `README.md` now treats `Lollipop.Final.theorem_one` as a conditional
  handoff endpoint and names a concrete certificate-free maximum theorem as
  the intended final target.
* `lake build Lollipop` was rerun successfully on June 22, 2026 and completed
  all 3320 jobs.
* Several closed arithmetic/table facts were changed from `native_decide` to
  ordinary kernel-checked Lean proofs.
* The refreshed `#print axioms Lollipop.Final.theorem_one` output is recorded
  verbatim in `README.md`; only three `native_decide` graph-classification
  certificates remain in that public theorem's axiom list.

## Verdict

**Yes. A complete, unconditional Lean formalization of the concrete lollipop problem is possible.**

What is impossible is the current attempt to construct geometry certificates for **every abstract problem family**. That is a problem with the abstraction boundary, not with the theorem.

The final theorem should have:

* no `GeometryCertificates` argument;
* no Euclidean or topological assumptions supplied by the caller;
* no `sorry`, project axioms, or externally trusted computations;
* a concrete definition of a lollipop, its complement, and its connected-component count;
* kernel-checked upper- and lower-bound proofs.

Explicitly defining the lower-bound arrangement is unavoidable: it is the mathematical witness proving attainment, but that witness can be constructed and verified inside Lean rather than accepted as a certificate.

## What exactly is impossible in the current architecture?

The current endpoint has the form

```lean
theorem theorem_one
    (P : TheoremOne.MaxProblemFamily)
    (h : GeometryCertificates P) :
    TheoremOneStatement P
```

Here, `P` is completely abstract. Its `region` function can be any function into `ℚ`; it need not count regions of Euclidean lollipops.

The supplied obstruction file demonstrates this with

```lean
zeroRegionMaxProblemFamily
```

whose region count is identically zero. At `n = 0`, its named maximum is therefore `0`, while the displayed lollipop formula gives `1`. Consequently,

```lean
GeometryCertificates zeroRegionMaxProblemFamily
```

would imply `0 = 1`.

Thus the exact impossible statement is essentially

```lean
∀ P : MaxProblemFamily, GeometryCertificates P
```

There is no corresponding contradiction for the **concrete Euclidean lollipop family**. For that family, the empty arrangement genuinely has one complementary region.

There is a second architectural issue. `MaxProblemFamily` already contains

```lean
aLop_spec :
  ∀ n, IsGreatest (Set.range (region n)) (aLop n)
```

So instantiating a concrete `MaxProblemFamily` requires proving in advance that `aLop` is the maximum: the main theorem one is trying to establish. The unconditional development should instead start from the existing weaker `ProblemFamily` notion, or avoid the abstraction entirely.

## The correct target theorem

A suitable concrete model is:

```lean
abbrev Point := EuclideanSpace ℝ (Fin 2)

structure Lollipop where
  center : Point
  radial : Point
  radial_ne_zero : radial ≠ 0
```

Using one nonzero radial vector is cleaner than storing a radius, anchor, ray direction, and an unrelated normalized angle. The vector determines everything:

```lean
def Lollipop.carrier (L : Lollipop) : Set Point :=
  {x | ‖x - L.center‖ = ‖L.radial‖} ∪
  {x | ∃ t : ℝ, 1 ≤ t ∧ x = L.center + t • L.radial}
```

This makes the ray automatically radial, outward, and attached to the circle at `center + radial`.

Then define

```lean
abbrev Arrangement (n : ℕ) := Fin n → Lollipop

def occupied (A : Arrangement n) : Set Point :=
  ⋃ i, (A i).carrier

def FreeSpace (A : Arrangement n) :=
  {x : Point // x ∉ occupied A}

noncomputable def regionCount (A : Arrangement n) : ℕ :=
  Nat.card (ConnectedComponents (FreeSpace A))
```

One must separately prove that the connected-component type is finite.

The final statement should be directly about the maximum:

```lean
theorem lollipop_maximum (n : ℕ) :
    IsGreatest
      (Set.range (fun A : Arrangement n => regionCount A))
      (candidate n)
```

It is usually easier to prove this as two theorems:

```lean
theorem region_upper
    (A : Arrangement n) :
    regionCount A ≤ candidate n

theorem region_lower
    (n : ℕ) :
    ∃ A : Arrangement n, regionCount A = candidate n
```

and then combine them into `IsGreatest`.

## A viable formalization route

### 1. Rebuild the concrete geometric layer

The present geometry structures should be replaced or wrapped by the single-vector model above. In particular, there should be no freely chosen `normalizedDirection` field that could disagree with the actual ray direction.

Prove elementary facts directly:

* the circle and stem are closed;
* the carrier is closed and connected;
* the stem starts at the circle;
* similarities carry lollipops to lollipops;
* similarities induce homeomorphisms of complements and preserve region counts.

These are ordinary Mathlib topology and Euclidean-geometry lemmas.

### 2. Define and prove finiteness of the region count

Mathlib already supplies `ConnectedComponents` as a quotient type, as well as one-point compactification infrastructure. ([Lean Community][1])

The key missing theorem is that a finite union of lollipop carriers has finitely many complementary components. This should not be inserted as an assumption. It follows from the fact that such a union is a finite tame embedded graph after compactification and subdivision.

The subdivision is finite because every pair of primitive pieces has one of a finite number of forms:

* two distinct circles meet in at most two points;
* a circle and a ray meet in at most two points;
* two non-collinear rays meet in at most one point;
* coincident circles are identical;
* collinear rays overlap in a point, segment, ray, or are disjoint.

After deduplicating coincident primitives and splitting at endpoints and isolated intersections, the compactified carrier union is a finite graph.

### 3. Prove the planar topological engine

This is the largest genuinely missing part.

There are two defensible approaches.

#### Route A: Follow the manuscript

Formalize the required special case of:

* one-point compactification of the plane;
* Mayer-Vietoris for the compactified carrier union;
* Alexander duality in dimension two;
* the relation between reduced `H_0` of the complement and the first cohomology of the carrier union.

Mathlib now has a basic singular chain and singular homology functor, but this does not make the required Alexander-duality argument automatic. ([Lean Community][2])

#### Route B: Prove a specialized embedded-graph theorem

This is the route I would recommend.

Prove directly that for a finite tame graph `K ⊂ S²`,

```text
#π₀(S² \ K) = 1 + β₁(K),
```

or equivalently prove the appropriate Euler face formula. It can be established by subdivision and induction on embedded arcs, with a polygonal or piecewise-smooth Jordan-curve theorem.

This remains substantial topology. The current official Mathlib issue for the Jordan curve theorem is still open and explicitly discusses developing the needed algebraic-topology machinery. ([GitHub][3]) Nevertheless, a specialized theorem for finite circular and linear arcs is much narrower than a full general Jordan theorem or general Alexander duality.

The resulting module should prove the exact arbitrary-degeneracy region inequality used in the manuscript, rather than assuming generic position.

### 4. Formalize all pair-intersection geometry

For each pair `(L_i, L_j)`, define the relevant number of connected components of the compactified intersection. Then prove inside Lean:

* the unrestricted pair bound;
* the close-pair saving;
* the intriguing-pair saving;
* the combined saving when both properties occur;
* all tangent, coincident, overlapping-stem, and anchor-degenerate cases.

Primitive intersection classifications should be proved from coordinate equations. Circle-circle and circle-ray calculations reduce to quadratic equations; ray-ray intersections reduce to linear dependence and order inequalities.

The forcing statements must then be proved:

* sufficiently many directions force a close pair;
* the inflated-circle argument forces an intriguing pair;
* the five-circle obstruction follows from the four-dimensional bilinear argument.

At that point, the existing colored-Zykov, weighted-Turan, blocker, and matrix-compression development can be connected to actual geometry.

### 5. Reuse the combinatorial backend only after a real build

The current combinatorial code appears substantial, but it has not received a fresh kernel build in the supplied environment. A text scan for `sorry` is not equivalent to type-checking.

The process should be:

1. Pin a stable Lean toolchain and exact Mathlib commit.
2. Run a clean `lake build`.
3. Repair every actual elaboration or API error.
4. Ensure the concrete geometric lemmas, rather than certificate fields, feed the combinatorial theorem.
5. Keep exhaustive Python or MILP checks only as corroboration; they must not occur in the trusted dependency chain.

### 6. Formalize the lower construction algebraically

The lower construction is especially suitable for certificate-free formalization.

Define the four rational base lollipops directly. Prove every required sign inequality using tactics such as:

```lean
norm_num
ring_nf
nlinarith
```

These tactics generate kernel-checked proof terms.

Then define the corrected local polynomial family directly as concrete lollipops. The vector formulation is particularly convenient:

```text
c_t = (3t, 3t),   v_t = (1 - t^2, -2t).
```

Since

```text
|v_t|^2 = (1 - t^2)^2 + 4t^2 = (1 + t^2)^2,
```

the circle radius is `1 + t^2`, while the stem is simply

```text
c_t + lambda v_t,   lambda >= 1.
```

This avoids square roots and normalization in the decisive algebra. Lean should prove the four primitive contributions

```text
2 + 1 + 0 + 1 = 4
```

by solving the corresponding polynomial equations, and should also prove transversality, distinctness, and anchor exclusions.

### 7. Replace analytic genericization by finite algebraic avoidance

The manuscript's real-analytic genericization is formalizable, but a finite algebraic argument is likely easier in Lean.

For fixed `n`, there are finitely many forbidden degeneracies:

* triple intersections;
* tangencies;
* anchors lying on another carrier;
* unwanted coincident primitives;
* parallel or collinear exceptional cases.

Using rational or polynomial parameterizations, each forbidden equality becomes a nonzero polynomial equation in finitely many perturbation parameters. Prove:

1. the desired pairwise intersection pattern is stable in an open parameter box;
2. a finite collection of nonzero polynomials cannot vanish everywhere on that box;
3. rational points are dense, so there is a rational perturbation in the box avoiding every forbidden polynomial.

This produces an explicit existence theorem inside Lean. No numerical search result needs to be trusted.

### 8. Assemble and audit the unconditional theorem

The final dependency chain should be:

```text
Concrete lollipop model
        ↓
Finite embedded-carrier graph and complement theorem
        ↓
Pair savings and geometric obstructions
        ↓
Colored extremal combinatorics
        ↓
Universal upper bound

Exact rational base
        ↓
Polynomial clusters
        ↓
Algebraic generic perturbation
        ↓
Universal lower construction

Upper + lower
        ↓
lollipop_maximum
```

The final source file should contain a theorem with no certificate argument:

```lean
#print axioms Lollipop.lollipop_maximum
```

The audit should verify:

* no `GeometryCertificates` in the theorem type or transitive assumptions;
* no `sorry`, `admit`, project `axiom`, or externally supplied truth values;
* no dependence on verification scripts;
* a clean build from an empty cache;
* only the ordinary foundational principles used by Lean/Mathlib, such as classical choice or quotient soundness, if the development uses them.

## Bottom line

The problem is formalizable. The present obstruction does **not** say otherwise. It says that arbitrary abstract `MaxProblemFamily` values cannot magically acquire Euclidean geometry.

The necessary correction is not "find better certificates." It is:

1. specialize to a concrete Euclidean lollipop type;
2. define regions as actual connected components;
3. prove the missing planar-topology theorem;
4. construct the geometric upper and lower inputs as ordinary Lean theorems;
5. target `IsGreatest` directly;
6. remove `GeometryCertificates` from the public theorem entirely.

The critical path is planar topology, not the finite combinatorics or polynomial arithmetic. Once that layer is supplied, there is no conceptual obstacle to a complete certificate-free theorem.

[1]: https://leanprover-community.github.io/mathlib4_docs/Mathlib/Topology/Connected/Clopen.html "Mathlib.Topology.Connected.Clopen"
[2]: https://leanprover-community.github.io/mathlib4_docs/Mathlib/AlgebraicTopology/SingularHomology/Basic.html "Mathlib.AlgebraicTopology.SingularHomology.Basic"
[3]: https://github.com/leanprover-community/mathlib4/issues/35222 "Jordan Curve Theorem (JCT) · Issue #35222 · leanprover-community/mathlib4 · GitHub"
