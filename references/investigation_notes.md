# Investigation Notes: `A_Colored_Turan_Proof_of_the_Lollipop_Formula`

Date: 2026-06-05

Original folder inspected read-only:

`/Users/siddhartha/Lossfunk/erdos_problems/problems/problem_a389624_lollipop_regions/A_Colored_Turan_Proof_of_the_Lollipop_Formula`

Working copy used for all edits/runs:

`/Users/siddhartha/Lossfunk/erdos_problems/problems/problem_a389624_lollipop_regions/colored_turan_proof_investigation_2026_06_05/source_copy`

## Summary

I did not find a mathematical counterexample to the combinatorial proof. The route

geometry -> two colored graphs -> colored Zykov quotient -> weighted blocker lemma -> `3 x 4` matrix theorem

appears internally coherent.  Neighboring audits in this problem directory reach the same distinction: the older restricted complete-multipartite/Gemini route is not a proof, while the later colored-blocker route appears to be the credible all-`n` argument.

The important caveat is now Lean coverage of the geometry/model layer rather than the combinatorial core.  After the continuation work below, Lean checks the blocker, formula, pair-summation, local compression algebra, global support descent, star-forest minimum, the full `3 x 4` matrix theorem, the partition-intersection bookkeeping, the quotient objective identity algebra, the weighted Turan theorem, the weighted-Turan-to-blocker step, the manuscript sorted-`S(n)` to internal labeled-extremum bridge, the concrete-model-to-final-certificate packaging, primitive lollipop carrier definitions, finite carrier-intersection crossing certificate interfaces, qoppa coordinate constructors from center/anchor data, the exact OEIS four-base coordinate definitions, the primitive-to-mathlib circle/ray bridge, the component bounds behind the generic carrier-intersection `<= 7` case, automatic finite carrier witnesses and automatic crossing tables from those component bounds via mathlib finite-set APIs, the seven-point lower-witness bridge for exact non-exceptional OEIS `= 7` pair certificates, exact carrier-intersection certificates for all six OEIS base pairs, no-meet circle certificates, `Metric.infDist`, orthogonal-projection, and determinant/Cauchy no-meet certificates for mixed circle-ray components, supporting-line-disjoint and parallel/offset determinant no-meet certificates for ray-ray components, the unordered normalized-direction close-pair-in-four theorem, Paulsen's circle-vector calculation and five-vector linear-algebra obstruction, the canonical circle intriguing relation, the restriction of global circle data to five-subsets, the expansion of the canonical four-case crossing-count table into the four older pointwise crossing inequalities, the exact-pairwise upper region algebra, the Karlsson lower crossing-to-region conversion, the four-cluster Karlsson lower crossing table and its equality with `lowerCrossingsOfQuad`, the named four-base Karlsson table with its `40` crossing / `45` region arithmetic, the clustered individual-pair Karlsson lower interface, the finite same/inter-cluster pair-count collapse from cluster fiber cardinalities, the pairwise-lower conversion that sums certified pair values to the aggregate Karlsson lower polynomial and derives the region equation from ordered insertion data, the four-base/local-blow-up-to-pairwise-lower conversion, the canonical four-fiber cluster witness for every admissible sorted quadruple, the automatic upgrade from ordinary named Karlsson lower data to the cardinality-clustered finite-counting interface, the geometric two-graph reduction from close/intriguing predicates, the colored-Zykov clone step, finite two-stage Zykov-extremal/twin-pair potential setup, the strict potential-increase contradiction for non-twin zero pairs, zero-twin colored quotient construction, colored quotient objective preservation, and the no-zero colored quotient to blocker-graph translation.  The package no longer uses global `axiom`/`constant` declarations.  What remains model-specific is proving the close/intriguing Euclidean route certificates giving `<= 5/4` savings and producing actual sorted Karlsson blow-up arrangements with the claimed pairwise crossing values and ordered insertion-region data.  The new cardinality-clustered, pairwise lower, four-base lower, finite-carrier, automatic-upper, and OEIS-seven-point layers prove the finite counting numerics in Lean; they do not by themselves prove that a concrete Euclidean blow-up realizes the canonical cluster labels geometrically.

## Lean Run

The original Lean package did not run as delivered in this environment:

- No system `lean`, `lake`, or `elan` was initially installed.
- I installed Elan locally under the investigation folder:
  `colored_turan_proof_investigation_2026_06_05/lean_toolchain`.
- `lake build` with no target reported:
  `warning: no targets specified and no default targets configured`
  and built nothing meaningful.
- `lake build Lollipop` on the copied files initially failed because current mathlib no longer has
  `Mathlib.Data.Rat.Basic`.
- The package has no pinned `lake-manifest.json`, so Lake fetched current mathlib and upgraded the Lean toolchain from the local `lean-toolchain` value `v4.15.0` to mathlib's current `v4.31.0-rc1`. This makes the Lean project non-reproducible as packaged.

Copy-only Lean patches applied:

- `Mathlib.Data.Rat.Basic` -> `Mathlib.Data.Rat.Defs` in:
  - `source_copy/lean/Lollipop/Algebra.lean`
  - `source_copy/lean/Lollipop/Core.lean`
- `constant` declarations in `Core.lean` -> `axiom` declarations. This does not make the formalization stronger; it just makes the intended assumed objects accepted by current Lean.

After these copy-only patches:

```text
lake build Lollipop
Build completed successfully (2953 jobs).
```

Interpretation: the copied Lean skeleton compiles after mechanical maintenance, but it does not machine-check the central theorem.

Continuation patches applied in the working copy:

- Added `source_copy/lean/Lollipop/Blocker.lean`.
  This proves the algebraic weighted-blocker inequality chain
  from the two weighted Turan lower bounds, `Q <= entrySq`, and the matrix-side lower bound.
- Added `source_copy/lean/Lollipop/CompressionAlgebra.lean`.
  This proves the local identities used in the matrix compression proof:
  four-cycle concavity, four-edge path linearity, the two double-star deletion formulas,
  the fact that at least one double-star deletion is non-increasing, the general Cauchy/star efficiency inequality,
  the two-edge star efficiency inequality,
  and the exceptional `(2,1,1)` star-forest cost identity.
- Added `source_copy/lean/Lollipop/Formula.lean`.
  This replaces the purely abstract formula layer with concrete finite extrema
  `concreteM` and `concreteS` over bounded integer quadruples, proves
  `concreteS n = (3/2)n^2 - concreteM n`, and proves that `concreteM n` is bounded above
  by the cost of any integer quadruple summing to `n`.
- Added `source_copy/lean/Lollipop/PairReduction.lean`.
  This proves the finite summation step from pointwise pair crossing estimates to the total crossing bound,
  the color-weight identity `1_D + 1_E + 1_{D cap E}`, and the final region-count algebra.
- Extended `source_copy/lean/Lollipop/Blocker.lean` with the quotient objective identity algebra and the theorem that the scalar partition-matrix side is exactly `matrixF U` for an explicit `3 x 4` matrix.
- Extended `source_copy/lean/Lollipop/Core.lean` with `CertifiedQuotient`.
  Given explicit `rho_3`, `rho_4`, matrix square-sum data, the two weighted Turan lower bounds,
  `Q <= entrySq`, and the matrix lower bound, Lean now proves the quotient blocker conclusion
  without using the old `weighted_blocker` axiom.
- Extended `source_copy/lean/Lollipop/Core.lean` further with `ConcreteCertifiedQuotient` and
  `ConcreteMatrixCertifiedQuotient`, which prove the quotient bound against the concrete finite formula
  `concreteS` instead of the abstract `S` axiom when the relevant certificate data are supplied.
- Removed the old global axiom-based path from `source_copy/lean/Lollipop/Core.lean`.
  It now contains no `axiom` or `constant` declarations.  The replacement structures are
  `CertifiedColoredPair`, `CertifiedLollipopUpper`, and `candidateRegions_isGreatest`, which prove
  the upper bound and exact attained maximum from explicit certificate data.
- Extended `source_copy/lean/Lollipop/Algebra.lean` with the finite max/min duality lemma behind
  `S(n) = 3/2 n^2 - M(n)`.
- Updated `source_copy/lean/Lollipop.lean` and `source_copy/lean/README.md` to include the new modules.
- Patched `source_copy/main.tex` in Appendix A to add the missing first-coordinate sign explanation before splitting the linear dependence into positive and negative sides.

After the continuation patches:

```text
env ELAN_HOME=.../colored_turan_proof_investigation_2026_06_05/lean_toolchain \
  PATH=.../colored_turan_proof_investigation_2026_06_05/lean_toolchain/bin:$PATH \
  lake build Lollipop

Build completed successfully (2961 jobs).
```

Current Lean interpretation: the package now checks the final algebraic implication, the concrete finite `S/M` duality, the blocker inequality algebra, the quotient objective algebra, the pairwise-to-total crossing summation, the local polynomial calculations used by support compression, the global support-compression theorem, the star-forest minimum, the full matrix theorem, the partition-intersection bookkeeping, the weighted Turan theorem, the weighted-Turan-to-blocker step, the unordered normalized-direction close-pair-in-four theorem via mathlib list sorting, Paulsen's circle-vector calculation, five-vector linear-algebra obstruction, canonical circle intriguing relation, restriction of one global circle-coordinate model to five-subsets, derived five-set intriguing-pair theorem from global circle-coordinate data, expansion of the canonical four-case crossing-count table into the four older pointwise crossing inequalities, exact-pairwise upper region algebra, primitive lollipop carrier definitions and finite carrier-intersection certificate interfaces, Karlsson lower crossing-to-region conversion, the four-cluster Karlsson lower crossing table and its equality with `lowerCrossingsOfQuad`, the clustered individual-pair Karlsson lower interface, the geometric two-graph reduction from close/intriguing predicates, the colored-Zykov clone step, finite two-stage Zykov-extremal/twin-pair potential setup, the strict potential-increase theorem for non-twin zero pairs, zero-twin colored quotient construction, colored quotient objective preservation, the no-zero colored quotient to blocker-graph translation, and the full colored Turan bound for arbitrary colored graphs satisfying the `D`/`E` forbidden-clique hypotheses.  It still does not constitute a full formal proof of the lollipop formula from first Euclidean principles because the canonical crossing-count table must still be proved for primitive lollipop carriers via finite carrier-intersection certificates, and the geometric construction of Karlsson blow-up arrangements realizing the clustered individual-pair table remains external or certificate-producing.

Latest endpoint patch:

- `GeometricPaulsenReduction.lean` now defines `canonicalCrossingCaseBound`, `PairwiseCanonicalCaseBoundGeometricLollipopUpper`, and `PairwiseCanonicalCaseBoundGeometricUpperCertificates`.  A proved conversion expands the single case table into `cross_le_general`, `cross_le_close`, `cross_le_intriguing`, and `cross_le_close_intriguing`.
- `TheoremOneFinal/Statement.lean` now exposes `CanonicalCaseBoundGeometricModelSubtheorems`, `MaxCanonicalCaseBoundGeometricModelSubtheorems`, `upper_bound_proven_from_canonical_case_bound_geometric_certificates`, `theorem_one_statement_proven_from_canonical_case_bound_geometric_certificates`, `theorem_one_formula_statement_proven_from_canonical_case_bound_geometric_certificates`, and `theorem_one_formula_at_proven_from_canonical_case_bound_geometric_certificates`.
- `CloseDirection.lean` now proves `exists_cyclicClose_pair_of_card_four`: any unordered four-set of normalized directions contains a close pair.  The proof uses `List.mergeSort` with the relation `theta x <= theta y`, plus the existing cyclic-gap pigeonhole theorem.
- `GeometricPaulsenReduction.lean` now defines `PairwiseCanonicalCoordinateGeometricLollipopUpper` and `PairwiseCanonicalCoordinateGeometricUpperCertificates`.  This is the strongest upper endpoint: global circle coordinates, global normalized directions, and one canonical crossing table; Lean derives the close-pair-in-four fact by sorting each four-set.
- `TheoremOneFinal/Statement.lean` now exposes `CanonicalCoordinateGeometricModelSubtheorems`, `MaxCanonicalCoordinateGeometricModelSubtheorems`, `upper_bound_proven_from_canonical_coordinate_geometric_certificates`, `theorem_one_statement_proven_from_canonical_coordinate_geometric_certificates`, `theorem_one_formula_statement_proven_from_canonical_coordinate_geometric_certificates`, and `theorem_one_formula_at_proven_from_canonical_coordinate_geometric_certificates`.
- `Lower.lean` now defines `LowerCrossingRealization` and proves `lowerRealization_of_lowerCrossingRealization`, deriving the old lower-region interface from Karlsson blow-up crossing counts plus `regions = crossings + n + 1`.
- `TheoremOne/Proof.lean` now defines `LowerCrossingRealizations` and proves `lowerRealizations_of_lowerCrossingRealizations` for problem families.
- `TheoremOneFinal/Statement.lean` now exposes `CanonicalCoordinateGeometricCrossingModelSubtheorems`, `MaxCanonicalCoordinateGeometricCrossingModelSubtheorems`, `upper_bound_proven_from_canonical_coordinate_geometric_crossing_certificates`, `theorem_one_statement_proven_from_canonical_coordinate_geometric_crossing_certificates`, `theorem_one_formula_statement_proven_from_canonical_coordinate_geometric_crossing_certificates`, and `theorem_one_formula_at_proven_from_canonical_coordinate_geometric_crossing_certificates`.
- `GeometricPaulsenReduction.lean` now defines `PairwiseCanonicalExactCoordinateGeometricLollipopUpper` and `PairwiseCanonicalExactCoordinateGeometricUpperCertificates`.  This exact-pairwise upper endpoint assumes pairwise counts and `regions = pairSum cross + n + 1`; Lean fills `crossings := pairSum cross` and `crossings_le_pairSum := le_rfl`.
- `TheoremOneFinal/Statement.lean` now exposes `CanonicalExactCoordinateGeometricCrossingModelSubtheorems`, `MaxCanonicalExactCoordinateGeometricCrossingModelSubtheorems`, `upper_bound_proven_from_canonical_exact_coordinate_geometric_crossing_certificates`, `theorem_one_statement_proven_from_canonical_exact_coordinate_geometric_crossing_certificates`, `theorem_one_formula_statement_proven_from_canonical_exact_coordinate_geometric_crossing_certificates`, and `theorem_one_formula_at_proven_from_canonical_exact_coordinate_geometric_crossing_certificates`.
- `TheoremOneManuscript/FormulaBridge.lean` now defines the manuscript's sorted `manuscriptS`, proves a four-number sorting/relabeling network preserves sum and square-sum while moving the penalty to a minimum-product pair, proves every labeled quadruple has a sorted relabeling with at least as much excess, and proves `concreteS n = manuscriptS n`.
- `TheoremOneManuscript/Statement.lean` now exposes the manuscript-facing displayed formula
  `P.aLop n = 4 * n.choose 2 + manuscriptS n + n + 1`
  and proves it from the strongest canonical-exact-coordinate final certificate package.
  It also defines a manuscript-facing exact-coordinate subtheorem package whose lower input is only
  sorted Karlsson crossing-count realizations, proves that the sorted finite maximum is attained,
  and derives lower attainment from sorted realizations alone.
- `TheoremOneManuscript/ConcreteModel.lean` now packages the remaining concrete model obligations
  as global extractor functions: centers/radii, positive radii, normalized stem directions, exact
  pairwise crossing counts, the canonical four-case crossing table, and
  `regions = pairSum cross + n + 1`.  Together with sorted Karlsson lower data, Lean converts these
  fields into the manuscript-facing theorem package and proves the maximum/formula statements.
- `TheoremOneManuscript/ExplicitInputs/PairCountedClusteredLower.lean` now constructs a canonical
  disjoint-union cluster map for every admissible quadruple using `Fintype.equivFinOfCardEq`, proves
  each fiber has the prescribed cardinality, derives the same/inter-cluster unordered pair counts
  from mathlib finite-cardinality lemmas, and upgrades ordinary named Karlsson lower data to the
  cardinality-clustered finite-counting interface.
- `TheoremOneManuscript/ExplicitInputs/PairCountedEndToEnd.lean` and
  `TheoremOneManuscript/PrimitiveGeometry/PairCountedEndToEnd.lean` now convert the older concrete,
  paper-style, primitive, and carrier-certified named blow-up subtheorem packages into the
  cardinality-clustered theorem stack.
- `TheoremOneManuscript/Formalization/TheoremOneFromSubtheorems.lean` now gives a compact theorem-facing
  statement alias `TheoremOneStatement` and proves the displayed formula from concrete, geometric,
  primitive, and carrier-certified named subtheorem packages through the cardinality-clustered chain.
- `TheoremOneManuscript/PrimitiveGeometry/SphereBridge.lean` now lifts the primitive
  `Fin 2 -> ℝ` coordinate plane to `EuclideanSpace ℝ (Fin 2)`, proves the custom squared distance
  `distSq2` is the squared `L^2` distance, identifies `circleSet` with the preimage of
  `EuclideanGeometry.Sphere`, identifies primitive rays/carriers with their lifted Euclidean
  versions, decomposes lifted carrier intersections into circle-circle, circle-ray, ray-circle, and
  ray-ray components, specializes mathlib's two-sphere intersection theorem to primitive
  circle-circle components, names each lifted ray's affine supporting line, proves circle-ray and
  ray-circle line/sphere at-most-two wrappers, proves a noncoincident ray-ray component is
  subsingleton, proves that nonzero primitive direction determinant implies distinct ray-supporting
  lines, exposes mathlib's `Sphere.secondInter` line/sphere theorem for a lollipop anchor,
  proves that any lifted ray/sphere intersection point is either the anchor or that second
  intersection, defines `CircleCircleNoMeetData` for far-apart or strictly nested disjoint circles,
  proves such certificates empty the circle-circle component, proves that they imply Paulsen's
  `circleIntriguingPair` predicate, defines `CircleRayNoMeetData` and `RayCircleNoMeetData` from
  `Metric.infDist` separation between a circle center and the other ray's supporting line, proves a
  ray-line orthogonal-projection helper whose distance is that `Metric.infDist`, proves the
  primitive determinant/Cauchy criterion saying that a supporting line misses a circle when
  `r^2 |v|^2 < det(anchor-center, v)^2`, proves that parallel ray directions with nonzero offset
  determinant have empty ray-ray component, and defines `RayRayNoMeetData` from disjoint supporting
  ray lines.
- `TheoremOneManuscript/PrimitiveGeometry/ComponentBounds.lean` now turns those component facts into
  finite cardinality bounds.  In particular, a finite lifted carrier-intersection witness has at
  most `7` points when the two circles and the two ray-supporting lines are noncoincident, and a
  primitive `PairwiseCarrierCrossingData` entry then satisfies `cross <= 7`.  It also defines
  `PairComponentSavings`, proves that component-wise caps imply the corresponding total finite
  carrier bound and rational crossing bound, and adds reusable constructors turning empty component
  facts, no-meet circle certificates, mixed-component `Metric.infDist`, orthogonal-projection, or
  determinant/Cauchy certificates, ray-ray supporting-line disjointness certificates, or parallel/
  offset determinant ray-ray certificates into `<= 5` and `<= 4` savings certificates.
- `TheoremOneManuscript/Formalization/TheoremOneFromComponentBounds.lean` now states a theorem-facing
  component-bound primitive carrier package and a stronger component-savings package, then proves
  Theorem 1 from either package plus named Karlsson blow-up lower data.  In the stronger endpoint,
  the generic `<= 7` pairwise crossing case is proved from carrier components and the close/
  intriguing `<= 5/4` cases are component-wise finite-cardinality obligations rather than final
  numeric crossing fields.
- `TheoremOneManuscript/FormalizedProof/` is a new non-disruptive manuscript-shaped subfolder.
  `Statements.lean` states the final displayed Theorem 1 target and the strongest known subtheorem
  package; `ManuscriptLemmas.lean` gives named proved endpoints for the region equation,
  close-pair-in-four, Paulsen five-intriguing-pair, generic component count, component-savings
  constructors, the no-meet-implies-intriguing branch, colored Turan theorem, and Section 5 matrix
  theorem; `TheoremOne.lean` proves the final formula from the strongest component-savings/Karlsson
  subtheorem package; `DependencyGraph.lean` exposes the direct proof-DAG theorem from the two
  remaining model-specific certificate producers, namely primitive carrier component-savings upper
  data and Karlsson four-base/local-blow-up lower data; `ManuscriptCatalogue.lean` adds a
  manuscript-label index for Theorem 1, the formal geometric-input layer, colored Zykov, weighted
  Turan, Section 5 support/star-forest/matrix endpoints, and the Karlsson lower-construction
  interface.
- `TheoremOneManuscript/PrimitiveGeometry/ComponentBounds.lean` now also defines
  `PrimitiveRadialCarrierComponentSavingsUpperGeometryData`, the radial-outward strengthening of the
  component-savings upper package.  `TheoremOneManuscript/FormalizedProof/DependencyGraph.lean` uses
  it in `RadialTheoremOneDependencyGraph`, and `ManuscriptCatalogue.lean` exposes
  `manuscript_theorem_one_from_radial_catalogued_lemmas` and
  `manuscript_theorem_one_at_from_radial_catalogued_lemmas` as the manuscript-closest Theorem 1
  endpoints from radial upper certificates plus Karlsson lower certificates.
- `TheoremOneManuscript/FirstPrinciples/Boundary.lean` is a new separate boundary module.  It names
  the exact current first-principles inputs as `EuclideanUpperCertificate`,
  `KarlssonLowerCertificate`, and `TheoremOneCertificates`, exposes projections for every remaining
  concrete upper/lower certificate field, and proves
  `theorem_one_from_first_principles_boundary` plus the single-size endpoint by routing those
  certificates through the radial manuscript catalogue endpoint.
- `TheoremOneManuscript/PrimitiveGeometry/Basic.lean` now also defines
  `LocalPairCarrierCrossingData`, so the primitive carrier crossing table can be supplied as one
  finite carrier-intersection certificate for each local pair `i < j`.  Lean assembles those local
  obligations into the old global `PairwiseCarrierCrossingData` through
  `PairwiseCarrierCrossingData.ofLocal`; `ManuscriptLemmas.lean` and
  `ManuscriptCatalogue.lean` expose this as `pairwise_carrier_crossing_data_from_local` and
  `manuscript_pairwise_carrier_crossing_data_from_local`.
- Added `TheoremOneManuscript/FirstPrinciples/LocalBoundary.lean`.  It defines
  `LocalEuclideanUpperCertificate`, replacing the global upper finite carrier-intersection field by
  local one-pair certificates, converts it to the existing `EuclideanUpperCertificate`, packages it
  with the same `KarlssonLowerCertificate` as `LocalTheoremOneCertificates`, and proves
  `theorem_one_from_local_first_principles_boundary` plus the single-size endpoint.
- `TheoremOneManuscript/ExplicitInputs/KarlssonBase.lean` now defines
  `KarlssonBaseSixPairTableCertificate`, a six displayed unordered inter-base value plus symmetry
  certificate for the Karlsson base table.  Lean proves that this expands to the universal ordered
  distinct-base-pair table agreement, defines `KarlssonBaseSixPairBlowUpIncrementalLowerData`, and
  converts it to the existing four-base/local-blow-up lower interface.  `LocalBoundary.lean` uses
  this as `LocalKarlssonLowerCertificate` and proves
  `theorem_one_from_fully_local_first_principles_boundary`.
- `TheoremOneManuscript/ExplicitInputs/KarlssonOEIS.lean` now routes the exact OEIS six-pair
  coordinate certificate through the generic local primitive carrier interface.  Each exact pair
  certificate converts to `LocalPairCarrierCrossingData`, the six-pair certificate supplies
  `localPairCarrierCrossingData` for every base pair `i < j`, and the all-pairs base-coordinate
  certificate is assembled by `PairwiseCarrierCrossingData.ofLocal`.
- `TheoremOneManuscript/RegionEquation.lean` now defines `OrderedIncrementStepData` and
  `StepwiseOrderedIncrementalPairRegionData`, so ordered region recurrences can be supplied as one
  local insertion-step certificate per step.  Lean assembles these into
  `OrderedIncrementalPairRegionData` and proves the same `regions = pairSum + n + 1` equation.
  `FirstPrinciples/LocalBoundary.lean` uses this to define stepwise fully local upper/lower
  certificates and proves `theorem_one_from_stepwise_fully_local_first_principles_boundary`.
- `TheoremOneManuscript/ExplicitInputs/KarlssonBase.lean` now also defines
  `LocalKarlssonBaseCopyPairCrossingData`, so the lower blow-up pair-value proof can be supplied
  one blown-up pair at a time.  Lean assembles those local copy-pair certificates into the universal
  `pair_cross_eq_base_copy` statement, defines
  `KarlssonBaseSixPairLocalBlowUpIncrementalLowerData`, and converts it to the existing pairwise
  lower interface.  `FirstPrinciples/LocalBoundary.lean` exposes the strongest current local
  endpoint as `PairStepwiseFullyLocalTheoremOneCertificates` and proves
  `theorem_one_from_pair_stepwise_fully_local_first_principles_boundary`.
- `TheoremOneManuscript/FirstPrinciples/LocalBoundary.lean` now defines
  `LocalEuclideanUpperPairData`, bundling one upper pair's finite carrier-intersection witness,
  generic circle/ray-line noncoincidence facts, and close/intriguing component-savings branches.
  The new `PairStepwiseLocalEuclideanUpperCertificate` assembles these all-pair local bundles into
  the previous stepwise local upper certificate, and
  `AllPairStepwiseFullyLocalTheoremOneCertificates` proves
  `theorem_one_from_all_pair_stepwise_fully_local_first_principles_boundary`.
- Patched `source_copy/main.tex` so the Section 5 Lean-status paragraph explicitly says the matrix
  theorem is no longer a Lean input, and so the lower-construction Lean-status remark names the
  six-entry, local copy-pair, and stepwise local certificate boundaries without overstating the Euclidean realization.
  Recompiled with `tectonic main.tex`; `main.pdf` is produced without TeX warnings.
- `TheoremOneManuscript/FormalizedProof/ManuscriptLemmas.lean` and `ManuscriptCatalogue.lean` now
  expose the Paulsen appendix relation-sign step and relation-splitting step as named Lean
  endpoints, together with the abstract five-vector Gram contradiction.  This matches the added
  manuscript sentence explaining why a nontrivial relation cannot have all coefficients with the
  same sign.
- `TheoremOneManuscript/ExplicitInputs/KarlssonBase.lean` now names the four-base Karlsson table
  separately from the blow-up data.  Lean proves the visible `5,7,7,7,7,7` table sums to `40`,
  packages those six entries plus symmetry as a table certificate, proves the base incremental
  equation gives `45` regions, defines both the theorem-facing and six-pair four-base/local-blow-up
  lower certificates, and converts those certificates to the pairwise lower interface.
- `TheoremOneManuscript/PrimitiveGeometry/Qoppa.lean` now formalizes the OEIS qoppa coordinate
  convention: primitive two-coordinate points, unit bearing vectors `(cos theta, sin theta)`, and
  `fromCenter`/`fromAnchor` constructors whose anchor-on-circle proof is derived from
  `Real.cos_sq_add_sin_sq`.  `PrimitiveGeometry/Basic.lean` now also names the non-disruptive
  predicate `EuclideanLollipop.IsRadialOutward`, since the primitive carrier record itself allows a
  general attached ray while the manuscript requires the half-line to extend radially outward; the
  two qoppa constructors are proved to satisfy this predicate.
- `TheoremOneManuscript/ExplicitInputs/KarlssonOEIS.lean` now records the exact OEIS four-base
  coordinates `Q0` through `Q3`, including `1.0488116827495215` as an exact rational, and proves the
  four base stems are radial outward plus the ordered base insertion arithmetic `1 -> 2 -> 8 -> 23 -> 45`.  The remaining base-coordinate
  theorem is explicitly named as `KarlssonOEISBaseCoordinateCrossingCertificate`, a finite
  carrier-intersection certificate for those exact four lollipops.  It is now also split into the
  modular `KarlssonOEISBaseSixPairCoordinateCrossingCertificate`; Lean converts the six individual
  pair certificates to generic `LocalPairCarrierCrossingData` and assembles them into the original
  all-pairs certificate.
- `TheoremOneManuscript/ExplicitInputs/KarlssonOEISGeometry.lean` now unwraps that base-coordinate
  certificate into the six displayed finite carrier-intersection cardinalities `5,7,7,7,7,7`,
  bundles them as `SixPairCardinalities`, proves all six OEIS base lifted-sphere noncoincidence
  facts, and proves all six OEIS base ray-supporting-line noncoincidence facts from exact direction
  determinants and sine positivity/antiperiodicity.  It packages the noncoincidence facts as uniform
  `i < j` theorems over `karlssonOEISBaseArrangement` and derives the generic `<= 7`
  crossing/cardinality bounds for every pair from any exact base carrier-intersection certificate.
- `TheoremOneManuscript/Formalization/TheoremOneFromComponentBounds.lean` and
  `TheoremOneManuscript/FormalizedProof/` now expose theorem-one endpoints from the
  four-base/local-blow-up Karlsson lower package, in addition to the pairwise lower package.
- `TheoremOneManuscript/FormalizedProof/ManuscriptLemmas.lean` now imports the OEIS geometry-facing
  layer and exposes the six-cardinality unwrapping theorem plus the determinant-to-ray-line
  noncoincidence route, all six exact OEIS base sphere facts, and all six exact OEIS base ray-line
  facts, plus the uniform OEIS genericity and derived `<= 7` facts as named manuscript-scale
  endpoints.
- `source_copy/main.tex` now also marks the lower blow-up construction's Lean boundary explicitly:
  Lean checks the finite table summation, pairwise-lower conversion, and ordered-insertion region
  algebra from `KarlssonBaseBlowUpIncrementalLowerData`; the Euclidean realization of those local
  blow-ups remains a model-specific geometric certificate.

Latest continuation build:

```text
env ELAN_HOME=.../colored_turan_proof_investigation_2026_06_05/lean_toolchain \
  PATH=.../colored_turan_proof_investigation_2026_06_05/lean_toolchain/bin:$PATH \
  lake build Lollipop

Build completed successfully (3289 jobs).
```

Latest placeholder scan:

```text
rg -n "^\s*(axiom|constant)\b|\bsorry\b|\badmit\b|opaque|unsafe|placeholder" source_copy/lean/Lollipop.lean source_copy/lean/Lollipop
```

returns no matches.

## TeX Run

On the copied manuscript:

```text
tectonic main.tex
```

compiled successfully and wrote `source_copy/main.pdf`.

Only warning:

```text
main.tex:66: Overfull \hbox (8.27441pt too wide)
```

After the Appendix A sign-explanation patch, `tectonic main.tex` still compiles successfully and writes `source_copy/main.pdf`.  The only warning remains the same overfull box at line 66.

## External Geometric Input

The manuscript's Lemma 1 is external geometry. Paulsen's page states the same close/intriguing setup:

- a close pair has at most 5 intersections;
- an intriguing pair has at most 5 intersections;
- a close and intriguing pair has at most 4 intersections;
- among 4 lollipops there is a close pair;
- among 5 lollipops there is an intriguing pair.

Paulsen's page explicitly says the second and third pairwise geometric statements are not written as formal proofs there, though he sketches the picture reasoning. The manuscript is therefore best read as a self-contained combinatorial proof after accepting those geometric inputs.

The appendix in this manuscript gives Paulsen's linear-algebra proof for the forced intriguing pair. The earlier sign-splitting gap has now been patched in the manuscript text: because the first component of every `v_i` is positive, a nontrivial linear relation cannot have all coefficients with the same sign. Lean exposes the corresponding formal step as `paulsen_relation_has_pos_and_neg_coefficients`, followed by `paulsen_relation_split`.

Local mathlib survey for closing the remaining Euclidean boundary:

- `Mathlib.Geometry.Euclidean.Basic` has `dist_smul_vadd_sq`, the quadratic equation for squared
  distance along a line.
- `Mathlib.Geometry.Euclidean.Sphere.SecondInter` has `EuclideanGeometry.Sphere.secondInter` and
  proves that a line through a point on a sphere meets the sphere only at that point and the computed
  second intersection.
- `Mathlib.Geometry.Euclidean.Sphere.Power` and `Sphere.Tangent` contain power-of-a-point and
  tangent/secant lemmas.

These are the right APIs for a first-principles lollipop-intersection proof, but the present
primitive layer uses a custom squared-coordinate `circleSet` over `Fin 2 -> ℝ`.  A future closure of
the Euclidean boundary should first bridge `circleSet` to `EuclideanGeometry.Sphere`, then prove the
finite circle-circle, circle-ray, and ray-ray intersection sets under explicit nondegeneracy and
perturbation hypotheses.

## Combinatorial Proof Audit

### Two-Graph Reduction

The reduction is correct assuming Lemma 1.

With

- `D = not close`,
- `E = not intriguing`,

the pointwise bound

```text
c_ij <= 4 + 1_{ij in D} + 1_{ij in E} + 1_{ij in D cap E}
```

has the right four cases:

- close and intriguing: at most 4;
- not close, intriguing: at most 5;
- close, not intriguing: at most 5;
- neither close nor intriguing: at most 7.

The clique obstructions also line up:

- `D` is `K_4`-free because among any four lollipops some pair is close;
- `E` is `K_5`-free because among any five lollipops some pair is intriguing.

### Colored Zykov Step

The symmetrization argument is now formalized in Lean. Cloning along color-0 pairs preserves both forbidden clique conditions because the derived `D` and `E` graphs are exactly `SimpleGraph.replaceVertex` after cloning, and mathlib supplies clique-freeness preservation for `replaceVertex`.  Lean proves finite objective-extremal and two-stage Zykov-extremal colored graphs exist, proves equal weighted color degrees across zero pairs in objective extremals, proves the clone-class cardinal bookkeeping for the twin-pair potential, and proves that any non-twin zero pair can be oriented so that cloning strictly increases the second-stage potential.  Therefore every color-zero pair in a two-stage Zykov extremal graph is a twin pair.

### Weighted Blocker Lemma

The weighted Turan inequalities are applied correctly:

```text
w(A) >= (rho_3(x) - Q)/2
w(B) >= (rho_4(x) - Q)/2
```

Intersecting minimizing 3- and 4-partitions gives a `3 x 4` matrix `U`. Since grouping class weights can only increase the sum of squares,

```text
Q <= sum u_ij^2,
```

and the sign is handled correctly:

```text
rho_3 + rho_4 - Q/2 >= rho_3 + rho_4 - (sum u_ij^2)/2 = F(U).
```

Thus the blocker lemma really reduces to the matrix theorem.

### Matrix Theorem

I checked the proof carefully and also wrote `audit_matrix.py`.

The compression lemma appears correct:

- cycle compression preserves row/column sums and uses concavity of `-1/2 sum u_ij^2`;
- four-edge path compression has zero quadratic coefficient and therefore a non-increasing endpoint exists;
- double-star compression has the stated differences
  `y(2B+2z-x)` and `y(2A+2x-z)`, and at least one is nonnegative.

The star-forest minimum proof also checks out. The enumeration of possible star-forest degree lists in `K_{3,4}` confirms that the only list with

```text
Gamma = sum 2t/(2t+1) > 2
```

is the intended exceptional list `(2,1,1)`, where `Gamma = 32/15`.

The script also exhaustively enumerated all nonnegative integer `3 x 4` matrices through total mass `n=12`; every case satisfied `F(U) >= M(n)`, with equality on the expected `K_{1,2} union K_2 union K_2` support.

This finite audit does not prove the theorem, but it supports the paper proof and did not expose a hidden non-star extremizer.

The continuation Lean work checks the same local compression formulas symbolically over `ℚ`, not just by finite enumeration:

- `pathCompressionPart_sub_zero` proves the four-edge path compression is linear in the compression parameter.
- `cycleCompressionSquarePart_sub_zero` proves the four-cycle alternating compression has negative quadratic coefficient.
- `doubleStarOld_sub_moveToX` and `doubleStarOld_sub_moveToZ` prove the manuscript's double-star differences.
- `doubleStar_some_move_not_increasing` proves that, for nonnegative masses, at least one of the two double-star deletions does not increase the objective.
- `exceptionalStarCost_eq_quadCost` proves the `(2,1,1)` normal form is exactly the four-cluster quadratic cost.

Additional continuation patches applied after this audit:

- `PairReduction.lean` now proves `pairFinset_card : (pairFinset n).card = n.choose 2` using mathlib's `Sym2` cardinality machinery, and exposes `pairSum_crossing_le_choose_plus_score`, the summed two-graph bound in the manuscript's `4 * binom(n,2)` form.
- `Upper.lean` now connects pointwise pair crossing estimates to the compact upper-bound certificates.  A `PairwiseCertifiedLollipopUpper` or `PairwiseDirectCertifiedLollipopUpper` contains the pairwise crossing functions, pointwise estimate, score-sum comparison, and colored-pair certificate; Lean derives the full lollipop upper bound and exactness theorem from those fields plus lower realization.
- `Algebra.lean` now proves the relabelling fact behind the sorted formula: moving the penalty to a pair with smaller product can only increase `clusterExcess`, and in a sorted nonnegative quadruple the first two entries have minimum pair product.
- `Formula.lean` now proves the small finite values `M(0)`, `M(1)`, `M(2)`, `M(3)`, the compact boundary theorem `M(n)=3n/2` for `n <= 3`, and the balanced-quadruple estimate `M(n) <= n^2/2` for `n >= 4`.
- `CompressionAlgebra.lean` now proves the star-degree efficiency arithmetic used in the non-exceptional star-forest branch: one or two components have efficiency sum at most `2`, and three positive components using at most seven vertices either have efficiency sum at most `2` or are the exceptional `(2,1,1)` degree list up to order.
- `Lower.lean` now formalizes the lower-bound algebra from Karlsson blow-up counts, proves that a finite maximizer of `concreteS n` exists, derives lower realizations from crossing-count realizations plus `regions = crossings + n + 1`, and proves exact greatestness from upper certificates plus a lower-realization hypothesis.
- `Core.lean` now includes direct matrix quotient certificates (`DirectMatrixCertifiedQuotient`, `DirectCertifiedColoredPair`, `DirectCertifiedLollipopUpper`) and both product and `Nat.choose` forms of the candidate formula.
- `TheoremOne/Statement.lean` and `TheoremOne/Proof.lean` now provide a new top-level theorem layer, separate from the earlier certificate modules.  Following mathlib's maximum idiom, Theorem 1 is first stated as
  `IsGreatest (regionSet P n) (candidateRegionsChoose n)`, which says the formula value is attained and every arrangement has at most that many regions.  The file also proves the named-function formula statement
  `P.aLop n = 4 * n.choose 2 + concreteS n + n + 1` whenever `aLop` is specified as the greatest attained region count.
- The main theorem names in the new layer are `theorem_one_maximum_from_pairwise_direct_certificates`,
  `theorem_one_formula_from_pairwise_direct_certificates`, and `theorem_one_formula_at`.
- `Matrix/Basic.lean` now states the matrix theorem for the exact Section 5 type, `NatMatrix := Fin 3 -> Fin 4 -> Nat`, as `MatrixTheoremStatement`.  It proves two unconditional branches of Section 5:
  `matrix_theorem_of_total_le_three` and `matrix_theorem_exceptionalStarNat`.
  It also proves `three_halves_entrySqNat_le_matrixFNat`, the general lower bound
  `F(U) >= (3/2) * sum_ij u_ij^2` for natural matrices.
- `Matrix/LocalMoves.lean` now proves the canonical four-cycle and four-edge-path compression identities directly for the actual `matrixF` definition:
  `matrixF_cycleMove_sub` and `matrixF_pathMove_sub`.
  It also proves endpoint non-increase lemmas
  `matrixF_cycleMove_endpoint_nonincreasing` and
  `matrixF_pathMove_endpoint_nonincreasing`.
- `Matrix/LocalMoves.lean` also now proves canonical double-star deletion identities directly for the actual `matrixF` definition:
  `matrixF_canonicalDoubleStar_sub_moveX` and `matrixF_canonicalDoubleStar_sub_moveZ`.
- `Matrix/Relabel.lean` now proves row/column relabeling invariance for `matrixTotal`, `matrixF`,
  `matrixTotalNat`, and `matrixFNat`, so canonical local moves can be transported to arbitrary rows
  and columns.
- `Matrix/Shapes.lean` now proves a finite support-shape classification:
  `isSupportStarForest_iff_canonicalShape`.  A support in `K_{3,4}` is a star forest iff it is a
  row/column relabeling of one of sixteen canonical masks.  This replaces informal star-forest
  shape enumeration with a checked finite theorem and will be the natural entry point for completing
  `StarForestMinimumStatement`.
- `Matrix/SignedMoves.lean` now proves the generic signed-compression endpoint engine:
  `matrixF_addDir_sub`, `endpoint_quadratic_nonpos`, and
  `matrixF_addDir_endpoint_nonincreasing`.
- `Matrix/Support.lean` now defines the finite support graph used by Section 5:
  `supportOfNat`, `supportCardNat`, `SupportAdj`, `HasSupportPath3`,
  `HasSupportPath4`, `HasSupportCycle4`, and `IsSupportStarForest`.
- `Matrix/Support.lean` also now includes the small finite graph fact
  `support_card_le_five_of_starForest`: a star-forest support in `K_{3,4}` has at most five edges.
  An attempted four-edge bound is false; the support
  `{(0,0),(0,1),(0,2),(1,3),(2,3)}` is a valid five-edge star forest.
- `Matrix/Strategy.lean` isolates the Section 5 global proof obligations:
  `SupportCompressionStatement`, `StarForestMinimumStatement`, and
  `SupportDescentStepStatement`.  Lean proves
  `support_compression_of_descent_step` by well-founded induction on support cardinality, and proves
  `matrix_theorem_of_descent_step_and_star_forest`, reducing compression to a one-step
  support-cardinality descent lemma plus the star-forest minimum.  Those two reduced obligations are
  discharged in `TheoremOneComplete/SupportDescent.lean` and
  `TheoremOneComplete/StarForestCases.lean`.
- `CompressionAlgebra.lean` now also proves the component inequalities
  `starCostFin_ge_total_sq`, `starCostFin_one`, `two_component_half_bound`, and
  `three_singleton_component_half_bound`.
- `Matrix/StarForest.lean` now connects those component inequalities to the finite minimum `M(n)`:
  one/two-component star bounds, the three-singleton bound, and the exceptional integer-quadruple
  branch all imply the required matrix lower bound once the corresponding component summaries are
  extracted from the support.
  It also proves `starForestMinimum_of_canonical_cases`, reducing
  `StarForestMinimumStatement` to `CanonicalStarForestMinimumCases`, i.e. one proof for each of the
  sixteen canonical support masks from `Matrix/Shapes.lean`.
  Consequently `matrix_theorem_of_descent_step_and_canonical_cases` proves the matrix theorem from
  the one-step support descent lemma plus those sixteen canonical star-forest cases.
  The first five canonical cases are proved in `Matrix/StarForest.lean`:
  `canonical_shape0_minimum`, `canonical_shape1_minimum`,
  `canonical_shape2_row_minimum`, `canonical_shape2_col_minimum`, and
  `canonical_shape2_singletons_minimum`.
- `TheoremOneComplete/StarForestCases.lean` now proves the remaining eleven canonical star-forest
  cases, packages all sixteen as `canonicalStarForestMinimumCases_proven`, and proves
  `starForestMinimum_proven`.
- `TheoremOneComplete/SupportDescent.lean` now proves the missing Section 5 global bookkeeping:
  a finite `native_decide` classification sends every non-star support, up to row/column relabeling,
  to a four-cycle, a row-oriented four-edge path, a column-oriented four-edge path, or an extended
  double-star envelope.  The file constructs the corresponding integer moves, proves total
  preservation, non-increase of `matrixFNat`, strict support-cardinality descent, and finally
  `support_descent_step_proven` and `matrix_theorem_proven : MatrixTheoremStatement`.
- `TheoremOneComplete/Proof.lean` adds a theorem-one assembly layer in which Section 5 is
  no longer an input field.  The remaining theorem-one inputs are the pairwise integral upper
  certificates and lower realizations for the chosen problem family.
- `TheoremOneComplete/PartitionMatrix.lean` formalizes the partition-intersection bookkeeping in
  the weighted blocker lemma.  Given a finite weighted quotient vertex set and maps to `Fin 3` and
  `Fin 4`, Lean constructs the `3 x 4` natural matrix, proves its row sums, column sums, and total
  mass, and proves
  `weightSquareSumRat_le_entrySqNat_partitionMatrixNat`, i.e. squaring after grouping can only
  increase the square sum.
- `TheoremOneEndToEnd/PartitionCertificates.lean` adds refined upper certificates in which the
  blocker matrix is no longer arbitrary data: it is generated from the actual quotient weights and
  the two weighted Turan partitions.  Lean now fills the integral matrix total field and the
  `Q <= entrySq` field automatically from `PartitionMatrix.lean`.  This layer has now also been
  strengthened so the quotient carries two blocker relations and weighted-Turan-style complement
  bounds; Lean derives the previous raw `a_lower` and `b_lower` fields internally.  It was then
  strengthened again so the quotient carries the concrete weighted objective equation `sigma_eq`;
  Lean derives `QuotientIdentity` internally instead of requiring it as a colored-pair field.
- `TheoremOneEndToEnd/WeightedTuran.lean` formalizes the algebraic interface for the weighted
  Turan step: the off-diagonal mass identity `n^2 - Q`, the split of an irreflexive relation and
  its off-diagonal complement, and
  `weightedEdgeMass_ge_of_complement_le_partition`, which derives
  `w(A) >= (rho - Q)/2` from a complement bound for a chosen partition.
  It now also proves `orderedRelWeight_partition_ne` and
  `orderedRelWeight_complement_le_of_crosses_partition`, so a structural certificate that every
  complement edge crosses the chosen partition automatically yields the numeric complement bound.
  This crossing condition is only a sufficient condition and is stronger than the weighted Turan
  theorem used by the manuscript.
- `TheoremOneEndToEnd/WeightedTuranTheorem.lean` now proves the weighted Turan theorem
  directly with mathlib's `SimpleGraph` API.  The proof formalizes ordered weighted edge mass,
  weighted degrees, clone row/column formulas for `replaceVertex`, the exact clone-replacement
  identity, ordered-weight extremal graphs, weighted-degree equality for nonadjacent positive
  vertices, transitivity of non-adjacency on the positive-weight support, colorability of the
  positive induced extremal graph, and the final partition bound
  `exists_partition_bound_of_cliqueFree`.
- `TheoremOneEndToEnd/WeightedTuranCertificates.lean` uses
  `exists_partition_bound_of_cliqueFree` to choose the `Fin 3` and `Fin 4` blocker partitions from
  actual blocker graphs whose complements are `K_4`-free and `K_5`-free.  It then converts those
  quotients into the partition-intersection/matrix certificate pipeline and proves the corresponding
  upper-bound theorem.
- `TheoremOneEndToEnd/ColoredZykov.lean` formalizes the colored-Zykov symmetrization in the
  manuscript's four-color quotient language.  It proves clone compatibility for the derived `D` and
  `E` graphs, the objective split around one vertex, finite existence of objective-extremal colored
  graphs, equal weighted color degrees across zero pairs in such extremal graphs, the ordered
  twin-pair potential corresponding to the manuscript's sum of squared clone-class sizes, existence
  of two-stage Zykov-extremal graphs maximizing that potential among objective maximizers,
  clone-class cardinal bookkeeping, strict potential increase for a non-twin zero pair under the
  larger-class orientation, and therefore the global zero-pair-implies-twin-pair theorem for
  two-stage Zykov extremals.
- `TheoremOneEndToEnd/ColoredZykovQuotient.lean` constructs the quotient colored graph.  It proves
  that Zykov extremality supplies the zero-twin quotient-ready condition, quotient color
  well-definedness, no off-diagonal zero color in the quotient, descent of `D`/`E` clique-freeness,
  quotient class-size weights, and the fact that class weights sum to the original vertex count.
- `TheoremOneEndToEnd/ColoredQuotientCertificates.lean` adapts no-zero colored quotients and
  original colored graphs into the weighted-Turan certificate pipeline.  It proves the weighted
  quotient objective formula `3P - 2a - 2b`, proves preservation of the ordered color objective under
  the zero-twin quotient with class-size weights, packages zero-twin-ready colored graphs as colored
  quotient certificates, proves the full colored Turan bound for arbitrary colored graphs satisfying
  the `D`/`E` forbidden-clique hypotheses, and exposes the strongest pairwise lollipop upper
  certificate layer whose graph-theoretic input is just the original colored graph.
- `TheoremOneEndToEnd/GeometricReduction.lean` formalizes the manuscript's geometric-to-colored
  reduction from explicit `close` and `intriguing` predicates.  Given the pair crossing table, the
  four geometric crossing cases, and the facts that every four vertices contain a close pair and
  every five vertices contain an intriguing pair, Lean constructs the colored graph, proves
  `D = not close` and `E = not intriguing`, proves the forbidden-clique hypotheses, proves the
  ordered color objective is twice the increasing-pair score sum, and produces the strongest
  colored-graph upper certificate.
- `TheoremOneEndToEnd/CloseDirection.lean` formalizes the normalized-direction pigeonhole fact behind
  the close-pair-in-four input: four cyclically ordered stem directions in `[0,1)` contain an
  adjacent cyclic gap at most `1/4`, hence a close pair for the canonical cyclic close relation.
- `TheoremOneEndToEnd/PaulsenLinearAlgebra.lean` formalizes the linear-algebra core of Paulsen's
  appendix.  It defines the symmetric form on `Fin 4 -> R`, proves the circle-coordinate calculation
  for `(1/r)(1, r^2 - |x|^2, x)`, proves the finite-dimensional dependence of five vectors in four
  dimensions using mathlib, splits the relation into positive and negative supports from the
  positive first coordinate, proves the small-side contradiction from Gram values in `(-1,0)`, and
  packages generic theorems deriving an intriguing pair in every five-set from Paulsen vector or
  circle-coordinate witnesses.
- `TheoremOneEndToEnd/GeometricPaulsenReduction.lean` converts upper certificates carrying
  Paulsen vector data, circle-coordinate distance-inequality data on five-subsets, or one global
  circle-coordinate model per arrangement into the existing geometric certificate layer by deriving
  the five-intriguing-pair field internally.  It also provides the strongest canonical-circle layer,
  where `intriguing` is definitionally Paulsen's non-obtuse circle relation from centers/radii, and
  the strongest canonical-geometric layer, where `close` is definitionally the cyclic normalized
  direction relation and the close-pair-in-four fact is derived internally.
- `TheoremOneEndToEnd/Proof.lean` adds the most expanded theorem-one statement layer:
  `theorem_one_maximum`, `theorem_one_formula`, and `theorem_one_formula_at`.  These prove Theorem 1
  from model-specific upper and lower certificate-production statements.  The newer final endpoint
  below exposes stronger variants whose upper input is only the manuscript's close/intriguing
  geometric data.
- `TheoremOneFinal/Statement.lean` adds a non-disruptive final endpoint using the mathlib
  `IsGreatest` idiom.  It names the remaining model-specific subtheorems, exposes the proved upper
  and lower halves, and proves the maximum and displayed formula statements from the imported
  subtheorem stack, including geometric-input, Paulsen-geometric, Paulsen-circle-geometric,
  global-circle-geometric, canonical-circle-geometric, and canonical-geometric variants.
- `source_copy/main.tex` was patched in the proof of Lemma `support compression` to make the
  formerly implicit Section 5 bookkeeping explicit: each move strictly decreases support
  cardinality, the allowed integer interval endpoints kill an existing positive edge without
  creating a new support edge, and the cycle/path/double-star cases cover every non-star support.
- `source_copy/main.tex` was also patched in Section `The lower construction` to make the
  dependence on Karlsson's four-lollipop base configuration from `CKS` explicit before applying the
  blow-up stability argument.
- `TheoremOneFormal/Dependencies.lean` and `TheoremOneFormal/Proof.lean` add a separate theorem-one
  layer in which quotient certificates carry an integral `NatMatrix`.  A single global
  `MatrixTheoremStatement` now generates all direct quotient matrix bounds, and the final theorem-one
  maximum/formula statement is proved from the named subtheorems
  `matrix_theorem`, `upper_certificates`, and `lower_realizations`.
  The same file also provides `DetailedTheoremOneSubtheorems`, whose Section 5 fields are
  `support_descent` and `star_forest_minimum`; Lean derives the matrix theorem from those fields
  before proving Theorem 1.
  It now also provides `CanonicalTheoremOneSubtheorems`, replacing the `star_forest_minimum` field by
  `canonical_star_forest_cases`, i.e. the sixteen canonical support-mask cases from the finite shape
  classification.

Updated Section 5 audit:

- I do not have a counterexample to the matrix theorem; exhaustive integer enumeration already supported it through total mass 12.
- A finite-support continuous optimization over all `2^12 - 1` nonempty support masks confirms that the expected exceptional `(2,1,1)` supports have continuous ratio `15/32`.
- That same support optimization found non-star support masks with continuous ratio below `1/2`, for example ratio `33/70`.  Therefore the manuscript cannot be repaired by a direct "all non-exception supports have `F >= n^2/2`" argument before compression.  The support-compression/descent step is genuinely necessary.
- The manuscript's Section 5 proof was missing explicit graph-theoretic bookkeeping for repeatedly finding cycles, four-edge paths, or double-stars and proving termination to star-forest normal form.  This is now filled in Lean by `support_descent_step_proven`, `support_compression_of_descent_step`, `starForestMinimum_proven`, and `matrix_theorem_proven`.

Current Lean verification:

```text
env ELAN_HOME=.../colored_turan_proof_investigation_2026_06_05/lean_toolchain \
  PATH=.../colored_turan_proof_investigation_2026_06_05/lean_toolchain/bin:$PATH \
  lake build Lollipop

Build completed successfully (3327 jobs).
```

Current TeX verification:

```text
tectonic main.tex

note: Writing `main.pdf`
```
The latest TeX run writes `main.pdf` without warnings.

Current placeholder scan:

```text
rg -n "^\s*(axiom|constant)\b|\bsorry\b|\badmit\b|opaque|unsafe" \
  source_copy/lean/Lollipop.lean source_copy/lean/Lollipop
```

returns no matches.

An older placeholder scan including the string `toPairwise` reports three matches in converter
names inside `TheoremOneEndToEnd/PartitionCertificates.lean`; those are false positives, not
placeholders or unsafe declarations.

## 2026-06-07 Manuscript-Facing Theorem 1 Formalization Update

- Added `TheoremOneManuscript/RegionEquation.lean`.  It proves the finite telescoping recurrence:
  if the partial region count starts at `1` and step `k < n` adds `added k + 1`, then the final
  count is `sum added + n + 1`.  The same file packages this as `IncrementalRegionData` and
  specializes it to the pair-sum crossing total.  It now also defines the canonical previous-pair
  contribution at insertion step `k` and proves that summing those contributions over
  `k = 0, ..., n - 1` is exactly `pairSum`.
- Extended `TheoremOneManuscript/ConcreteModel.lean` with
  `CanonicalExactUpperGeometryIncrementalData` and `ConcreteIncrementalModelSubtheorems`.  These
  allow the strongest manuscript-facing Theorem 1 statement to be proved from step-by-step
  previous-pair insertion-region data rather than assuming the pair-sum region equation directly.
- Extended `TheoremOneManuscript/Statement.lean` and `ConcreteModel.lean` with incremental sorted
  lower-realization interfaces.  Lean now derives the lower `regions = crossings + n + 1` equation
  from `IncrementalRegionData`, and `ConcreteFullyIncrementalModelSubtheorems` proves the displayed
  Theorem 1 formula from incremental upper and lower region data.
- Added `TheoremOneManuscript/Proof.lean` as the final manuscript-facing entry point, with
  `theorem_one_maximum`, `theorem_one`, and `theorem_one_at` using the fully incremental concrete
  package.
- Added `TheoremOneManuscript/GeometricInputs.lean`, which matches the paper's abstract
  close/intriguing geometric input style.  It proves the manuscript sorted-`S(n)` Theorem 1 formula
  from `PairwiseGeometricUpperCertificates` plus sorted Karlsson lower data, and also has an
  incremental lower variant.  `Proof.lean` now exposes
  `theorem_one_from_geometric_inputs` and `theorem_one_at_from_geometric_inputs`.
- Extended `GeometricInputs.lean` with explicit global extractor packages
  `ManuscriptGeometricUpperData`, `ManuscriptGeometricIncrementalUpperData`,
  `ManuscriptGeometricDataSubtheorems`, and
  `ManuscriptGeometricFullyIncrementalDataSubtheorems`.  These make the remaining Euclidean
  upper-bound boundary concrete: total crossings, close/intriguing predicates, decidability,
  symmetry, exact pairwise crossing table, the baseline `cross <= 7`, the close/intriguing
  improvements `<= 5` and `<= 4`, the four-/five-subset facts, and the incremental region equation.
  `Proof.lean` now also exposes `theorem_one_from_geometric_data` and
  `theorem_one_at_from_geometric_data`.
- Added the checked theorem
  `ManuscriptGeometricUpperData.pair_crossing_le_four_plus_score`, plus its incremental variant,
  proving the manuscript's displayed estimate
  `c_ij <= 4 + 1_D + 1_E + 1_{D cap E}` directly from the four geometric crossing fields.  This
  explicitly uses the newly stated baseline `cross <= 7` case.
- Patched `source_copy/main.tex`, Lemma `geometric lollipop input`, to explicitly state the baseline
  fact that any generic pair of lollipops has at most `7` crossings.  This was required for the
  neither-close-nor-intriguing case in the displayed pointwise estimate
  `c_ij <= 4 + 1_D + 1_E + 1_{D cap E}` and already appears in Lean as `cross_le_general`.
  `tectonic main.tex` succeeds after the patch, with only the pre-existing overfull hbox warning at
  line 66.
- Patched the Section 5 matrix proof text in `source_copy/main.tex` to make two formal conventions
  explicit: the edge-pair sum in the expanded `F(U)` formula is over unordered adjacent support-edge
  pairs, and a star forest in `K_{3,4}` has at most three nonempty components because each component
  uses a row vertex.  These match the Lean support-shape classification and star-forest case split.
- Patched the colored-Zykov proof text in `source_copy/main.tex` to spell out the two-stage
  extremal choice used in Lean: first maximize the colored objective, then maximize the ordered
  twin-pair potential.  The new paragraph explains why a color-zero non-twin pair can be cloned
  without lowering `sigma` while strictly increasing the potential, matching
  `sameRow_of_zero_of_zykov_extremal`.
- Patched the weighted Turan proof text in `source_copy/main.tex` to expose the positive-weight
  support argument checked in Lean: in an extremal graph, nonadjacent positive-weight vertices have
  equal weighted neighborhoods; nonadjacency is transitive on the positive support; the induced
  positive-support graph is complete multipartite and `r`-colorable; zero-weight vertices can then
  be assigned arbitrarily.  This matches `positive_induce_colorable_of_cliqueFree_extremal` and
  `exists_partition_bound_of_positive_induce_coloring`.
- Added a separate Lean subfolder, `TheoremOneManuscript/ExplicitInputs/`, so the strengthened
  endpoint does not disturb the earlier manuscript interfaces.  `ExplicitInputs/Lower.lean` defines
  named Karlsson blow-up construction data: for each sorted quadruple it supplies the produced
  arrangement, the proof that its crossing count is `lowerCrossingsOfQuad q`, and either the direct
  lower region equation or incremental insertion data.  Lean proves that this construction-shaped
  package implies the older sorted lower-realization interfaces and lower attainment.  The companion
  file `ExplicitInputs/EndToEnd.lean` combines this lower package with either concrete upper geometry
  or paper-style close/intriguing upper data and proves the displayed Theorem 1 formula.  `Proof.lean`
  now exposes the short wrappers `theorem_one_from_explicit_blowup` and
  `theorem_one_from_geometric_data_and_explicit_blowup`.
- Added `ExplicitInputs/LowerTable.lean`.  It defines the four-cluster Karlsson lower table as the
  six displayed unordered cluster pairs: intra-cluster contribution `4`, exceptional inter-cluster
  pair `(0,1)` contribution `5`, and the other five inter-cluster pairs contribution `7`.  Lean
  proves the table sum is exactly `lowerCrossingsOfQuad`, converts table-certified lower data to the
  named blow-up lower interface, and the end-to-end/proof files now expose `theorem_one_from_table_blowup`,
  `theorem_one_from_geometric_data_and_table_blowup`,
  `theorem_one_from_primitive_geometry_and_table_blowup`, and
  `theorem_one_from_primitive_carrier_geometry_and_table_blowup`.
- Added `ExplicitInputs/ClusteredLower.lean`.  It adds the individual-lollipop cluster-map layer:
  each constructed lollipop has a label in `Fin 4`, the four fibers have the requested quadruple
  sizes, individual unordered pairs are counted by the symmetric same-cluster/exceptional/inter-cluster
  Karlsson table, and the individual pair sum collapses to the four-cluster table.  Lean converts this
  clustered data into the table-certified lower interface.  The theorem wrappers now include
  `theorem_one_from_clustered_blowup`, `theorem_one_from_geometric_data_and_clustered_blowup`,
  `theorem_one_from_primitive_geometry_and_clustered_blowup`, and
  `theorem_one_from_primitive_carrier_geometry_and_clustered_blowup`.
- Added `ExplicitInputs/PairCountedClusteredLower.lean`.  This removes the direct
  pair-sum-to-table equality from the strongest lower finite-counting interface.  Lean first proves
  that the individual-pair sum is the oriented `4 x 4` cluster-label count table, proves the
  same-cluster subset count `#s choose 2` using the same `Sym2`/`pairFinset` method as
  `pairFinset_card`, proves that the two orientations between disjoint fibers add to the product of
  the fiber cardinalities, and therefore derives the whole Karlsson `4/5/7` table from only the four
  cluster fiber cardinalities.  It exposes pair-counted, fiber-counted, and cardinality-only lower
  construction packages.
- Added `ExplicitInputs/PairCountedEndToEnd.lean`,
  `PrimitiveGeometry/PairCountedEndToEnd.lean`, and
  `TheoremOneManuscript/Formalization/PairCountedProof.lean`.  These give theorem-one endpoints for
  the pair-counted, fiber-counted, and cardinality-only clustered lower interfaces, including
  primitive-coordinate and carrier-certified primitive-coordinate variants.  The strongest new short
  aliases are `theorem_one_from_cardinality_clustered_blowup`,
  `theorem_one_from_geometric_data_and_cardinality_clustered_blowup`,
  `theorem_one_from_primitive_geometry_and_cardinality_clustered_blowup`, and
  `theorem_one_from_primitive_carrier_geometry_and_cardinality_clustered_blowup`.
- Added `TheoremOneManuscript/PrimitiveGeometry/`.  `Basic.lean` defines a coordinate lollipop as a
  circle set plus a ray set in `R2`, proves basic carrier/anchor facts, defines finite coordinate
  lollipop arrangements, defines pairwise carrier-intersection sets, and packages primitive exact
  upper geometry data.  It also adds a stronger finite carrier-crossing certificate whose
  `crossingPoints` finite set is required to be exactly the carrier-intersection set and whose
  cardinality is the numeric pair crossing table.  The same crossing table is now splittable into
  local one-pair certificates through `LocalPairCarrierCrossingData`, and Lean reassembles them into
  `PairwiseCarrierCrossingData` with `PairwiseCarrierCrossingData.ofLocal`.  Lean converts these primitive records to
  `CanonicalExactUpperGeometryIncrementalData` by extracting centers, radii, and normalized stem
  directions.  `EndToEnd.lean` combines primitive upper geometry with the named Karlsson lower
  construction, the table-certified lower variant, and the clustered lower variant; `Proof.lean` exposes
  `theorem_one_from_primitive_geometry_and_explicit_blowup`,
  `theorem_one_from_primitive_carrier_geometry_and_explicit_blowup`, and the corresponding
  table-certified and clustered endpoints.
- Added `TheoremOneManuscript/FormalizedProof/`.  This is a separate proof-skeleton subfolder for
  the user's requested shape of the formalization: Theorem 1 is stated as the final displayed
  formula, the manuscript-scale lemmas are named as proved Lean endpoints, and the final theorem is
  proved from the strongest component-savings primitive-carrier/Karlsson lower subtheorem package.
  It now also contains `DependencyGraph.lean`, a direct proof-DAG theorem from primitive carrier
  component-savings upper data plus Karlsson four-base/local-blow-up lower data to the displayed
  Theorem 1 statement.
  The component layer now also has constructors turning empty circle/ray component facts into
  `PairComponentSavings` witnesses for the close/intriguing `<= 5` and `<= 4` obligations, including
  the new mixed-component line-separation/projection-distance/determinant and ray-ray no-meet/
  parallel-determinant certificate routes.
- Added `ExplicitInputs/PairwiseLower.lean` and exposed it through
  `Formalization/TheoremOneFromComponentBounds.lean` and `FormalizedProof/TheoremOne.lean`.  This is
  the current strongest lower-bound-facing theorem endpoint: the input supplies the constructed
  arrangement, a cluster witness, pairwise crossing values, a proof that those pair values match the
  Karlsson cluster table, and ordered insertion-region data.  Lean then sums the pair values to the
  aggregate Karlsson lower polynomial and derives the region equation before proving the final
  Theorem 1 statement from the component-savings upper package.
- Added `ExplicitInputs/KarlssonBase.lean`, `PrimitiveGeometry/Qoppa.lean`, and
  `ExplicitInputs/KarlssonOEIS.lean`.  The first names the four-base Karlsson table and proves the
  `40` crossing / `45` region arithmetic, the second formalizes qoppa constructors from center or
  anchor data using mathlib trigonometry, and the third records the exact OEIS four-lollipop base
  coordinates plus the ordered insertion arithmetic.  `TheoremOneFromComponentBounds.lean` and the
  `FormalizedProof` layer now expose Theorem 1 endpoints from the four-base/local-blow-up lower
  package.
- Added `ExplicitInputs/KarlssonOEISGeometry.lean`.  This does not prove the finite intersection
  certificate from scratch, but once that certificate is supplied it now proves the six concrete
  finite carrier-intersection set cardinalities for the displayed Karlsson base table, and records
  all six sphere and all six ray-line noncoincidence facts for the exact OEIS coordinates.  It also
  packages these as uniform genericity fields and derives the generic `<= 7` bounds from the
  existing component-count theorem.
- Patched `source_copy/main.tex` so the Section 5 Lean-status paragraph no longer overfulls and so
  the lower-construction section explicitly identifies `KarlssonBaseBlowUpIncrementalLowerData` as
  the Lean boundary for the local blow-up realization.
- Verified `lake build Lollipop` again after the change; the build completes successfully with
  3288 jobs, and the placeholder scan over `Lollipop.lean` and `Lollipop/` still returns no
  matches.

## Remaining Caveats Before Treating This As Final

1. The proof is not fully internally Lean-formalized from first geometric principles.  The Lean
   package now has no global axioms/placeholders and checks Section 5's matrix theorem, the weighted
   Turan theorem, the partition-intersection matrix algebra, the quotient objective identity algebra,
   the normalized-direction close-pair-in-four theorem, Paulsen's circle-vector calculation,
   five-vector linear-algebra obstruction, canonical circle intriguing relation, and restriction of
   global circle-coordinate data to five-subsets, primitive lollipop carrier definitions and
   carrier-intersection certificate interface, generic `2+2+2+1 <= 7` component-count theorem,
   component-savings-to-crossing-bound theorem, no-meet circle certificates for far-apart/strictly
   nested circles, the no-meet-implies-intriguing branch, mixed-component `Metric.infDist`,
   orthogonal-projection, and determinant/Cauchy no-meet certificates, ray-ray supporting-line and
   parallel/offset determinant no-meet certificates, and empty-component/no-meet savings
   constructors, stepwise ordered region-increment assembly, the weighted-Turan-to-blocker step, the blocker algebra, finite pair-summation algebra, lower
   construction algebra including the named Karlsson blow-up data interface, the four-cluster
   lower crossing table, the clustered individual-pair lower interface, and the derivation of all
   finite same/inter-cluster pair counts from cluster fiber cardinalities, the pairwise lower
   conversion from certified pair values and ordered insertion data to aggregate Karlsson lower
   data, the geometric two-graph
   reduction from close/intriguing predicates, colored
   Zykov through the global zero-pair-implies-twin-pair theorem, zero-twin colored quotient
   construction, colored quotient objective preservation, the no-zero colored quotient to blocker
   translation, and the theorem-one assembly.  It still does not construct the remaining
   model-specific certificates from primitive definitions: Euclidean proofs of the pairwise
   crossing-count facts by explicit finite carrier-intersection sets for the primitive lollipop
   carriers, extraction of normalized
   direction/circle-coordinate data for concrete lollipops, and primitive coordinate/local-perturbation
   construction of the named Karlsson blow-up arrangements realizing the claimed pairwise table and
   ordered insertion-region data remain
   external theorem/certificate boundaries.

2. The working-copy Lean package now has `lean-toolchain` set to
   `leanprover/lean4:v4.31.0-rc1` and `lake-manifest.json` pins mathlib to
   revision `859caf703c2ec80952bad6c1cd102b3f14eabf5b`.  The original source
   folder may still need those reproducibility files promoted if it is to be used directly.

3. Paulsen's linear-algebra contradiction, circle-vector Gram calculation, canonical Paulsen circle
   relation, and restriction of one global circle-coordinate model to every five-subset are now
   checked in Lean.  The close-pair-in-four step is also checked from ordered normalized direction
   data.  Primitive lollipop carriers, automatic finite carrier-intersection witnesses, and the
   exact OEIS base finite witnesses are now named in Lean, but a fully first-principles manuscript
   would still need to prove the pairwise close/intriguing crossing bounds by producing the
   remaining route certificates and connect concrete lollipop geometry to the coordinate/direction
   certificates.

4. The lower construction is now represented in Lean by named construction-data packages, including
   four-cluster table-certified, clustered individual-pair, pair-counted, fiber-counted,
   cardinality-only clustered, and pairwise ordered-insertion variants, not only an existential
   realization relation.  The finite pair-counting part is internal: same-cluster and inter-cluster
   pair counts are derived from the four cluster fiber cardinalities, and the pairwise endpoint sums
   certified pair values to the aggregate lower polynomial.  It still relies on Karlsson's
   four-lollipop configuration and on the self-intersection/blow-up stability of lollipops.  The
   manuscript cites the base configuration explicitly at the lower-construction lemma; a fully
   first-principles version would still include coordinates/local perturbation details.

5. The missing first-component sentence in Appendix A has been patched in the working copy.  The original source folder still has the older text unless the working-copy patch is promoted.

6. The strongest first-principles upper boundary has been refined again.  In
   `FirstPrinciples/LocalBoundary.lean`, `RoutedLocalEuclideanUpperPairData`
   lets each local pair supply named geometric route constructors for the
   close/intriguing `<= 5` and close-and-intriguing `<= 4` branches instead of
   a raw component-savings object.  The route constructors are defined in
   `PrimitiveGeometry/ComponentBounds.lean` and cover disjoint/nested circle
   cases, projection-distance and determinant/Cauchy mixed circle-ray
   separation, and parallel-offset ray-ray separation.  Lean proves the routed
   all-pair first-principles boundary implies manuscript Theorem 1.  The main
   `FormalizedProof/DependencyGraph.lean` layer now also has routed and
   routed-radial proof-DAG endpoints, so the catalogue can derive Theorem 1
   directly from named route certificates.

7. The exact OEIS four-base region arithmetic has also been localized.  In
   `ExplicitInputs/KarlssonOEIS.lean`,
   `karlssonOEISBaseStepwiseOrderedRegionData` supplies the four insertion
   steps `1 -> 2 -> 8 -> 23 -> 45` as `OrderedIncrementStepData` certificates,
   and the formalized-proof catalogue exposes the resulting stepwise
   `45 = 40 + 4 + 1` endpoint.

8. One concrete direction fact from the OEIS coordinates is now checked rather
   than left implicit: `ExplicitInputs/KarlssonOEISGeometry.lean` proves the
   exceptional base pair `(Q0,Q1)` is close in the canonical cyclic
   normalized-direction relation.  This was an early coordinate step toward
   the finite carrier-intersection certificate, which is now completed in the
   complete-formalization layer.

9. The mixed circle-ray no-meet toolkit was strengthened with a half-line
   outward criterion: if a ray starts outside a circle and its direction has
   nonnegative dot product away from the circle center, then the ray misses the
   circle even if the full supporting line intersects it.  This is now a named
   `PairComponentSavingsFiveRoute` branch.  The exact OEIS pair `(Q0,Q1)` has
   a checked instance: the `Q1` ray starts outside the `Q0` circle and points
   away, so the `circle(Q0) ∩ ray(Q1)` component is empty and Lean obtains a
   concrete `<= 5` component-savings route for that close pair.

10. Component-savings crossing bounds now work directly from one local
    `LocalPairCarrierCrossingData` certificate, not only after assembling the
    global `PairwiseCarrierCrossingData` table.  This matches the strongest
    local first-principles boundary more tightly: a single pair certificate
    plus a single savings route immediately yields the rational bound for that
    table entry.

11. A new non-disruptive Lean subfolder,
    `TheoremOneManuscript/CompleteFormalization/`, now indexes the strongest
    current endpoint.  Its `Proof.lean` restates manuscript Theorem 1, names
    the automatic-upper/routed-savings/stepwise-local-lower certificate
    boundary as `CompleteCertificate`, exposes local generic/close/intriguing
    pair-bound lemmas, records Section 5's proved matrix theorem, and proves
    `theorem_one` and `theorem_one_at` from that strongest boundary.

12. The concrete OEIS `(Q0,Q1)` route is now connected all the way through the
    local exact pair certificate.  The two coordinate inequalities behind the
    route are named separately: the `Q1` ray anchor is outside the `Q0`
    circle, and the `Q1` ray direction points weakly away from the `Q0`
    center.  Lean uses these to prove the direct empty-component theorem
    `circle(Q0) ∩ ray(Q1) = ∅` in lifted component form.  From a six-pair OEIS
    base-coordinate certificate, Lean then proves both
    `karlssonBasePairCrossing (0 : Fin 4) (1 : Fin 4) <= 5` and the finite-set
    form `C.pair01.crossingPoints.card <= 5`.  This still does not construct
    the finite set itself, but it proves the exceptional pair's saving from
    the route plus one local carrier-intersection witness.

13. The exact `(Q0,Q1)` circle relation is also now classified: Lean proves
    Paulsen's strict obtuse-intersection condition for the two base circles,
    hence the pair is not intriguing.  This lets
    `ExplicitInputs/KarlssonOEISGeometry.lean` build a full
    `PrimitiveRoutedLocalPairData` object for `(Q0,Q1)` from the six-pair local
    finite carrier-intersection certificate: the close branch uses the
    half-line-outward route, while the intriguing and close-intriguing route
    branches are discharged by contradiction.  `FirstPrinciples/LocalBoundary`
    now promotes any such primitive local routed record to the
    first-principles `RoutedLocalEuclideanUpperPairData` record, and
    `CompleteFormalization/Proof.lean` uses that conversion for `(Q0,Q1)`.

14. The new `CompleteFormalization/OEISGeometry.lean` file now proves the
    exact finite-intersection geometry for the exceptional base pair
    `(Q0,Q1)` without changing the older files.  Lean names the forward-time
    ray-ray intersection point where the `Q1` ray reaches the `Q0` x-axis ray.
    It also names the two x-axis points of `ray(Q0) ∩ circle(Q1)`,
    `((9 - sqrt 57) / 20, 0)` and `((9 + sqrt 57) / 20, 0)`, and proves that
    the ray-circle component contains only those two points.  For
    `circle(Q0) ∩ circle(Q1)`, Lean proves the radical-axis relation
    `20045 * x + 40 * y = 3`, verifies the two explicit radical-coordinate
    circle-circle witnesses, and classifies the circle-circle component by
    those two witnesses.  Combining this with the empty
    `circle(Q0) ∩ ray(Q1)` route and the unique ray-ray point, Lean proves a
    five-point finset whose coercion is exactly the primitive `(Q0,Q1)`
    carrier intersection, proves its cardinality is `5`, proves any supplied
    six-pair certificate has exactly that finite set for `pair01`, and builds
    the local `(0,1)` coordinate crossing certificate directly.  After the
    later `(Q0,Q2)`, `(Q0,Q3)`, `(Q1,Q2)`, `(Q1,Q3)`, and `(Q2,Q3)`
    completions, the exact OEIS four-base finite-witness work is closed in
    Lean.

15. `CompleteFormalization/FiniteCarrier.lean` now closes the generic finite
    witness existence gap.  Using mathlib's `Set.Infinite.exists_subset_card_eq`
    and `Set.Finite.toFinset`, Lean turns the existing component bounds
    (`2+2+2+1`) into actual finite primitive carrier-intersection `Finset`
    witnesses under lifted-sphere and ray-supporting-line noncoincidence.  It
    proves each witness is exactly the primitive carrier intersection, proves
    its cardinality is at most `7`, defines the automatic crossing table by
    these cardinalities, and bundles the resulting
    `PairwiseCarrierCrossingData` automatically.

16. `CompleteFormalization/AutomaticUpper.lean` changes the final theorem
    boundary: the upper side no longer asks for local finite carrier witnesses
    as independent input fields.  Instead, `RoutedStepwiseCertificate` asks for
    the noncoincidence facts, close/intriguing route constructors, the stepwise
    region recurrence for the automatic table, and radial-outward stems.  Lean
    constructs the local carrier certificates from `FiniteCarrier.lean` and
    converts the result into the older routed all-pair first-principles
    boundary.  `CompleteFormalization/Proof.lean` now uses this automatic
    upper boundary as `CompleteCertificate` and also exports the six-entry
    Karlsson base table, the `40` crossing sum, the `45` base-region theorem,
    and the canonical four-fiber cluster witness.

17. `CompleteFormalization/OEISSevenPoint.lean` now reduces each of the five
    remaining non-exceptional OEIS base-pair certificates to a concrete
    seven-point lower witness.  Since the automatic finite carrier witness
    already proves `<= 7`, a seven-point finite subset of the primitive carrier
    intersection proves that automatic witness has cardinality exactly `7` and
    therefore gives a `KarlssonOEISBasePairCoordinateCrossingCertificate`.
    The file also defines `SevenComponentWitness`, matching the geometric
    decomposition `2 + 2 + 2 + 1`: two circle-circle points, two circle-ray
    points, two ray-circle points, and one ray-ray point, all distinct.  This
    is the Lean shape used for each non-exceptional exact OEIS base pair.

18. `CompleteFormalization/OEISPair02.lean` now completes the concrete witness
    for the non-exceptional pair `(Q0,Q2)`.  It proves the `Q2` trigonometric
    direction identities, constructs the ray-ray point, the two
    `ray(Q0) ∩ circle(Q2)` points, the two `circle(Q0) ∩ ray(Q2)` points, and
    the two `circle(Q0) ∩ circle(Q2)` points, proves their lifted component and
    primitive carrier-intersection memberships, proves all required
    distinctness facts, packages them as a seven-point finset/subset, derives
    automatic finite-witness cardinality `= 7`, and exports the exact local
    `(0,2)` coordinate crossing certificate.

19. `CompleteFormalization/OEISPair03.lean` now completes the analogous
    concrete witness for `(Q0,Q3)`.  It proves the `Q3` trigonometric
    direction identities for the `pi/30` direction, constructs all seven
    component points, proves their lifted component and primitive
    carrier-intersection memberships, proves the required distinctness facts,
    packages the seven-point finset/subset, derives automatic finite-witness
    cardinality `= 7`, exports the exact local `(0,3)` coordinate crossing
    certificate, and exposes these facts through the complete Lean index.

20. Section 5's matrix theorem has been audited against the Lean dependency
    chain.  The theorem is not an input: `support_descent_step_proven` and
    `starForestMinimum_proven` imply
    `matrix_theorem_proven : MatrixTheoremStatement`, with support descent
    routed through a finite relabeling/exhaustion of `K_{3,4}` support masks.
    The manuscript's support-compression proof text now says this explicitly,
    rather than leaving the graph-classification step implicit.  A new
    non-disruptive Lean folder,
    `TheoremOneManuscript/StatementProof/`, states the displayed Theorem 1
    formula with `manuscriptS`, exposes the proved support-compression,
    star-forest, matrix, and formula-bridge subtheorems, and proves the final
    formula from the current `ModelData`/`CompleteCertificate` boundary.

21. `CompleteFormalization/OEISPair23.lean` now completes the exact
    seven-component witness for `(Q2,Q3)`.  Lean proves the ray-ray
    intersection using the determinant simplification
    `-sin(pi/6) = -1/2`, proves the two mixed quadratic pairs
    `circle(Q2) ∩ ray(Q3)` and `ray(Q2) ∩ circle(Q3)`, proves the two
    equal-radius circle-circle points, lifts all seven component memberships,
    proves the required pairwise distinctness facts, packages the seven-point
    finset/subset, derives automatic finite-witness cardinality `= 7`, and
    exports the exact local `(2,3)` coordinate crossing certificate.

22. `CompleteFormalization/OEISPair12.lean` now completes the exact
    seven-component witness for `(Q1,Q2)`.  Lean proves the ray-ray
    intersection, the two `circle(Q1) ∩ ray(Q2)` points, the two
    `ray(Q1) ∩ circle(Q2)` points, and the two circle-circle points, proves
    the lifted component and primitive carrier-intersection memberships,
    proves the required pairwise distinctness facts, packages the seven-point
    finset/subset, derives automatic finite-witness cardinality `= 7`, and
    exports the exact local `(1,2)` coordinate crossing certificate.

23. `CompleteFormalization/OEISPair13.lean` now completes the exact
    seven-component witness for `(Q1,Q3)`.  Lean proves the needed
    trigonometric bounds for the tiny `Q1` bearing and the `Q3` direction,
    constructs the ray-ray point, both mixed quadratic pairs, and both
    circle-circle points, lifts all seven component memberships, proves the
    pairwise distinctness facts, packages the seven-point finset/subset,
    derives automatic finite-witness cardinality `= 7`, and exports the exact
    local `(1,3)` coordinate crossing certificate.

24. `TheoremOneManuscript/StatementProof/Boundary.lean` now makes the final
    theorem-facing `ModelData` boundary auditable.  It defines
    `UpperRouteRegionData` for the remaining automatic-upper route/region
    certificate fields, `LowerBlowUpData` for the remaining stepwise local
    Karlsson blow-up fields, combines them as `ConstructionData`, proves
    `ConstructionData ≃ ModelData`, and proves the displayed Theorem 1 formula
    from this split construction boundary.

25. The close-direction part of the Euclidean route interface is now
    formalized.  `PrimitiveGeometry/DirectionBridge.lean` uses mathlib's
    trigonometric lemmas to prove
    `dot2 (angleDirection a) (angleDirection b) = cos(a-b)` and that a
    cyclic-close pair of normalized directions in `[0,1)` has nonnegative
    bearing-vector dot product.  `PrimitiveGeometry/NormalizedBearing.lean`
    names the missing compatibility condition between a lollipop's stored
    `rayDirection` and its `normalizedDirection`, proves it for qoppa
    constructors up to one full turn, and derives the corresponding
    nonnegative dot-product fact for actual ray vectors in compatible
    arrangements.  `ExplicitInputs/KarlssonOEIS.lean` now proves this
    normalized-bearing compatibility for all four exact OEIS base qoppas, and
    `StatementProof/Subtheorems.lean` exposes both the general bridge and the
    exact OEIS `(Q0,Q1)` actual-ray dot-product consequence.  This closes the
    angle-to-dot portion of the close-pair route story, but it does not by
    itself prove the full close/intriguing route-savings theorem for arbitrary
    lollipop pairs.

26. `PrimitiveGeometry/CloseRouteAudit.lean` records an exact audit example
    showing that a tempting shortcut for the close-pair route theorem is
    false.  Two unit qoppas with shared anchor `(1,0)`, one pointing right and
    one pointing down, are radial outward, have normalized-bearing
    compatibility, and are cyclic-close at the `3/4` boundary.  Lean proves
    that the shared anchor lies in both mixed components
    `circle(right) ∩ ray(down)` and `ray(right) ∩ circle(down)`.  This does
    not contradict the expected close-pair `<= 5` bound, but it shows the
    proof cannot proceed by claiming that close radial pairs always make one
    mixed component empty.  This particular audit pair is now positively
    certified by the direct-overlap theorem in item 28, but arbitrary
    close-route formalization still needs a coupled component-count argument
    or a richer direct carrier-bound route than the current component-empty
    constructors.

27. `PrimitiveGeometry/CarrierSavings.lean` adds that richer direct
    carrier-bound interface.  `PairCarrierSavings L M b` states directly that
    every finite subset of the whole lifted carrier intersection has
    cardinality at most `b`, without requiring independent component caps.
    Lean proves that the existing `PairComponentSavings` and named
    `PairComponentSavingsFiveRoute`/`PairComponentSavingsFourRoute`
    certificates convert into this direct interface, and proves direct
    carrier-savings certificates imply the corresponding rational crossing
    bound from both global pairwise carrier data and local one-pair carrier
    witnesses.  `Formalization/TheoremOneFromComponentBounds.lean` now also
    exposes theorem-facing direct-savings packages: direct whole-carrier upper
    savings plus either named Karlsson lower data, pairwise lower data, or
    four-base/local-blow-up lower data imply the displayed Theorem 1 formula.
    This does not yet prove the close-route theorem, but it gives the formal
    shape needed for a future coupled component-count proof.

28. `PrimitiveGeometry/OverlapSavings.lean` proves the first direct coupled
    component-count routes.  If a point lies in any three of the four lifted
    components `circle-circle`, `circle-ray`, `ray-circle`, and `ray-ray`, or
    if two overlap witnesses together improve all four component estimates,
    and the two lifted circles and ray-supporting lines are noncoincident,
    then every finite subset of the whole carrier intersection has cardinality
    at most `5`; if one point lies in all four components, the bound improves
    to `4`.  The proof deletes the overlap witness points and uses
    mathlib/Finset cardinality bounds on the remaining filtered component
    witnesses.  Lean uses the four-component theorem in
    `PrimitiveGeometry/CloseRouteAudit.lean` to prove
    `closeRouteAudit_direct_savings_four`, so the shared-anchor audit pair is
    not merely a negative example; it has an actual direct
    `PairCarrierSavings ... 4` certificate.  Separately,
    `TheoremOneManuscript/AuditedTheoremOne/` is now a new theorem-facing
    folder that states Theorem 1, records the relevant mathlib bridge tools,
    packages all currently proved generic manuscript subtheorems, isolates the
    remaining model-specific construction data, and proves Theorem 1 from
    that construction boundary.

29. The lower-bound boundary is now monotone as well as exact.  In
    `TheoremOneManuscript/Statement.lean`, Lean defines
    `SortedLowerCrossingBoundRealization` and its incremental version: a
    construction may prove only
    `lowerCrossingsOfQuad q <= crossings A`, together with the usual region
    recurrence, and Lean derives an arrangement with at least the candidate
    number of regions.  In
    `ExplicitInputs/PairwiseLower.lean`,
    `PairwiseCardinalityClusteredKarlssonBlowUpIncrementalLowerBoundData`
    asks each unordered copy pair only to have crossing value at least the
    Karlsson cluster-table value.  Lean proves the finite unordered-pair sum
    inequality and derives lower-bound attainment.  This reduces the future
    concrete blow-up geometry obligation: exact classification of every extra
    pair intersection is no longer needed for the lower-bound half, only
    lower witnesses for the `4/5/7` table values and ordered insertion-region
    data.

30. The monotone lower interface is now wired through the theorem-one
    endpoints rather than only proving a standalone lower-bound lemma.
    `Statement.lean` proves
    `maximumStatement_of_choose_upper_bound_and_lower_bound_attainment`: the
    usual upper bound plus an arrangement with at least the candidate region
    count forces exact maximum attainment.  `Formalization/TheoremOneFromComponentBounds.lean`,
    `FormalizedProof/Statements.lean`, and `FormalizedProof/TheoremOne.lean`
    expose component-savings and direct-savings theorem packages with
    monotone pairwise lower data.  `FirstPrinciples/LocalBoundary.lean`,
    `CompleteFormalization/AutomaticUpper.lean`,
    `CompleteFormalization/Proof.lean`, and
    `StatementProof/Boundary.lean` now also have automatic-upper/local
    first-principles theorem endpoints whose lower input is local
    `>=` cluster-value data rather than exact copy-pair equality.  Finally,
    `PrimitiveGeometry/LowerWitness.lean` proves the local geometric bridge:
    a finite set of distinct points inside one primitive carrier intersection,
    together with the ordinary local carrier-crossing certificate for the full
    pair intersection, supplies the corresponding local monotone copy-pair
    lower certificate.  Lean proves the needed cardinality comparison by
    embedding the lower subset into the certified full crossing finset.

31. The automatic-upper boundary now accepts direct whole-carrier savings.
    `CompleteFormalization/AutomaticUpper.lean` defines
    `DirectSavingsStepwiseCertificate`, whose pairwise crossing table and
    finite carrier witnesses are still constructed automatically from
    noncoincident spheres and ray-supporting lines, but whose close and
    intriguing inputs are direct `PairCarrierSavings` certificates rather than
    routed component-savings constructors.  It converts this data to
    `PrimitiveCarrierDirectSavingsUpperGeometryData` and proves theorem-one
    endpoints with both exact local Karlsson lower data and monotone local
    lower inequalities.  `CompleteFormalization/Proof.lean` exposes these as
    `CompleteDirectSavingsCertificate` and
    `CompleteDirectSavingsMonotoneLowerCertificate`, and
    `StatementProof/Boundary.lean` exposes split construction boundaries for
    direct-savings upper data.  This means the overlap-savings theorems from
    item 28 can feed the final theorem boundary directly; they no longer need
    to be repackaged as independent component-empty route certificates.

32. A new separate Lean folder,
    `TheoremOneManuscript/EndToEndFormalization/`, now combines the automatic
    upper and monotone lower refinements without changing the older theorem
    stack.  `AutomaticLower.lean` defines
    `StepwiseMonotoneCarrierSubsetLowerCertificate`: for each produced sorted
    blow-up arrangement, the pair table agrees with the automatic
    finite-carrier table, and each unordered pair has a finite lower subset
    inside its primitive carrier whose cardinality dominates the required
    Karlsson cluster value.  Lean uses
    `FiniteCarrier.localPairCarrierCrossingDataOfFiniteCarrierEq`,
    `automaticCarrierCrossingTable_eq_card`, and
    `LocalPairCarrierLowerSubsetData.toLocalClusterPairLowerBoundData` to
    assemble a
    `FirstPrinciples.StepwisePairLocalKarlssonLowerBoundCertificate`.
    `EndToEndFormalization/Proof.lean` then proves Theorem 1 endpoints from
    either routed automatic upper data or direct whole-carrier savings upper
    data plus these automatic lower carrier-subset certificates.
    `CompleteFormalization/Proof.lean` re-exports these as
    `CompleteAutomaticLowerCertificate` and
    `CompleteDirectSavingsAutomaticLowerCertificate`.

33. The automatic lower boundary now has a Nat-valued Karlsson-size
    specialization.  `ExplicitInputs/ClusteredLower.lean` defines
    `karlssonClusterPairCrossingNat`, the `4/5/7` table as natural numbers,
    and proves `karlssonClusterPairCrossing_eq_nat`, so the rational
    cluster-table lower bound is exactly the coercion of that Nat size.
    `EndToEndFormalization/AutomaticLower.lean` defines
    `StepwiseKarlssonCarrierSubsetLowerCertificate`, where a concrete
    construction supplies lower subsets of those Nat table sizes directly,
    with no separate proof that the size dominates the rational cluster
    entry.  `EndToEndFormalization/Proof.lean` and
    `CompleteFormalization/Proof.lean` expose routed and direct-savings
    theorem-one endpoints from these `4/5/7` lower-subset certificates.

34. The new `EndToEndFormalization/` folder now has the explicit
    statement/subtheorem/proof shape requested for Theorem 1.
    `Subtheorems.lean` names the proved bridge lemmas used by the most
    concrete current
    endpoint: the Nat/rational Karlsson table equality, the automatic
    carrier-table cardinality identity, lower-subset-to-local-monotone-lower
    conversion, automatic-lower-to-first-principles conversion, direct-savings
    upper conversion, and the direct-savings/`4/5/7` lower-subset theorem.
    `Statement.lean` states `TheoremOneStatement`, defines
    `DirectSavingsCertificate` for the more general direct-savings boundary,
    defines `StrongestCertificate` as the overlap-witness automatic-upper plus
    Nat-valued Karlsson lower-subset/cardinality boundary, and proves
    `theorem_one` and `theorem_one_at` from the overlap-witness endpoint.  The
    root `Lollipop.lean` imports this statement layer.

35. The upper close/intriguing obligation has been reduced one step further
    for the overlap route.  `EndToEndFormalization/OverlapUpper.lean` defines
    `PairComponentFiveOverlap`, a concrete certificate saying either one
    point lies in any three carrier components or two witnesses together
    improve all four component estimates, and
    `PairComponentAllFourOverlap`, a concrete certificate that one point lies
    in all four components.  Lean converts these witnesses into
    `PairCarrierSavings ... 5` and `PairCarrierSavings ... 4` using the
    already proved overlap theorems, packages them as
    `OverlapSavingsStepwiseCertificate`, and converts that to the automatic
    direct-savings upper boundary.  `EndToEndFormalization/Proof.lean`,
    `Subtheorems.lean`, `Statement.lean`, and
    `CompleteFormalization/Proof.lean` now expose Theorem 1 endpoints from
    overlap-witness upper data plus automatic lower carrier subsets,
    including the Nat-valued Karlsson `4/5/7` lower-subset boundary.  The root
    build now checks 3322 Lean jobs.

36. The lower side now also has an automatic-cardinality variant.
    `EndToEndFormalization/AutomaticLower.lean` defines
    `StepwiseKarlssonCarrierCardLowerCertificate`: instead of supplying an
    explicit lower subset for each produced pair, the construction may prove
    directly that the automatic finite carrier witness has cardinality at
    least the Nat-valued Karlsson `4/5/7` table value.  Lean then uses that
    automatic carrier finset itself as the lower subset, via the proved
    `arrangementPairIntersectionFinset_spec` equality, and converts to the
    same monotone local lower boundary.  `EndToEndFormalization/Proof.lean`,
    `Subtheorems.lean`, `Statement.lean`, and
    `CompleteFormalization/Proof.lean` now expose direct-savings and
    overlap-witness theorem endpoints from these automatic carrier-cardinality
    lower bounds.  The clean `Statement.lean` headline `StrongestCertificate`
    now uses overlap-witness upper data plus these automatic carrier-card
    lower bounds.

37. The theorem-facing lower boundary no longer asks for an arbitrary
    cluster witness.  `EndToEndFormalization/AutomaticLower.lean` now defines
    `StepwiseCanonicalKarlssonCarrierCardLowerCertificate`, which uses
    `ExplicitInputs.cardinalityClusteredKarlssonTableWitnessOfSortedQuad`
    internally.  A concrete lower construction only supplies produced
    arrangements, primitive arrangements, noncoincident sphere/ray-line facts,
    automatic pair-table agreement, ordered insertion-region data, and
    cardinality lower bounds for the automatic carrier finsets against the
    canonical sorted-quad cluster labels.  `EndToEndFormalization/Proof.lean`
    adds direct-savings and overlap-witness theorem endpoints from this
    canonical-cardinality lower boundary; `Subtheorems.lean`,
    `Statement.lean`, and `CompleteFormalization/Proof.lean` expose the
    corresponding named subtheorems and complete-formalization aliases.  The
    clean headline `StrongestCertificate` is now the overlap-witness upper
    boundary plus canonical automatic carrier-cardinality lower bounds.

38. The exact OEIS four-base lower table is now proved for the automatic
    finite carrier, not just for the older coordinate-crossing certificates.
    The new `EndToEndFormalization/OEISBaseLower.lean` file proves that the
    exceptional `(Q0,Q1)` automatic carrier finset has cardinality `5`, by
    identifying it with the exact five-point carrier-intersection finset from
    `CompleteFormalization/OEISGeometry.lean`.  It then reuses the five
    seven-point non-exceptional witnesses to prove automatic cardinality `7`
    for `(Q0,Q2)`, `(Q0,Q3)`, `(Q1,Q2)`, `(Q1,Q3)`, and `(Q2,Q3)`, and
    packages all six increasing pairs as
    `automatic_witness_card_eq_karlssonClusterPairCrossingNat` plus the
    corresponding inequality form.  `CompleteFormalization/Proof.lean`
    re-exports these as the exact automatic OEIS base lower table.  This
    removes another base-table bridge from the remaining construction
    obligations; the still-open lower work is the sorted blow-up/perturbation
    realization for arbitrary sorted quadruples.

39. The exact OEIS base lower table now also matches the theorem-facing
    canonical cluster labels in the all-ones base case.  The Nat-valued
    `karlssonClusterPairCrossingNat` table is proved symmetric, the exact
    base automatic carrier table is upgraded to an unordered pair theorem,
    and `OEISBaseLower.lean` defines the all-ones sorted quadruple, Lean's
    canonical cardinality-cluster witness for it, and the exact OEIS base
    arrangement relabeled by that canonical cluster map.  Lean proves the
    canonical cluster map is injective from the fact that each canonical fiber
    has cardinality one, obtains the relabeled sphere/ray-line noncoincidence
    facts, and proves
    `canonicalOneOneOneOne_automatic_witness_card_eq_karlssonClusterPairCrossingNat`.
    `CompleteFormalization/Proof.lean` re-exports the relabeled arrangement
    and the equality/inequality forms.  This means the theorem-facing
    canonical lower boundary is already realized for the exact four-base
    all-ones case; arbitrary sorted blow-up perturbations remain open.

40. The canonical all-ones OEIS base lower result now reaches the local
    monotone lower interface, not only a raw cardinality inequality.
    `OEISBaseLower.lean` defines the automatic pair-crossing table for the
    canonical relabeled exact base arrangement, constructs the local
    carrier-crossing certificate from the automatic finite carrier, uses the
    automatic carrier finset itself as a `LocalPairCarrierLowerSubsetData`,
    and converts this to `LocalClusterPairLowerBoundData` for every increasing
    pair.  The theorem
    `canonicalOneOneOneOne_pairCross_ge_cluster` is the direct inequality form
    consumed by the monotone pairwise lower pipeline.  `CompleteFormalization/Proof.lean`
    re-exports the automatic pair table, local lower subset, local lower
    certificate, and inequality form.

41. The canonical all-ones OEIS base case now has a matching Lean upper table,
    and therefore exact equality with the Karlsson cluster table.  The new
    `EndToEndFormalization/OEISBaseUpper.lean` file adds symmetry for direct
    whole-carrier savings, turns the concrete `(Q0,Q1)` half-line-outward route
    into a `PairCarrierSavings ... 5` certificate in both orientations, uses
    the generic noncoincident carrier theorem for all other distinct canonical
    base pairs, and proves
    `canonicalOneOneOneOne_pairCross_le_karlssonNat`.  Combining this with
    the lower inequality from `OEISBaseLower.lean` gives
    `canonicalOneOneOneOne_pairCross_eq_cluster`, an exact equality between
    the canonical all-ones automatic pair table and the rational Karlsson
    cluster table.  `CompleteFormalization/Proof.lean` re-exports the direct
    savings certificates, upper inequality, and exact equality.

42. The ordered region recurrence now has table-transport lemmas.  In
    `RegionEquation.lean`, Lean proves `previousPairSum_congr` and
    `previousPairAdded_congr`, then uses them to define
    `OrderedIncrementalPairRegionData.congr_cross`,
    `OrderedIncrementStepData.congr_cross`, and
    `StepwiseOrderedIncrementalPairRegionData.congr_cross`.  These show that
    ordered or stepwise insertion-region certificates can be reused whenever
    two crossing tables agree pointwise.  This does not solve the remaining
    geometric insertion-region obligation, but it removes a pure bookkeeping
    obstacle for later relabeling or automatic-table substitutions.

43. The exact canonical all-ones OEIS table is now summed in Lean.  After
    proving the pairwise equality
    `canonicalOneOneOneOne_pairCross_eq_cluster`, `OEISBaseUpper.lean` derives
    `canonicalOneOneOneOne_pairSum_eq_clustered`,
    `canonicalOneOneOneOne_pairSum_eq_lowerCrossingsOfQuad`,
    `canonicalOneOneOneOne_pairSum_eq_forty`, and
    `canonicalOneOneOneOne_region_eq_pairSum_add`.  These show that the
    canonical automatic pair table has aggregate crossing sum `40` and the
    checked base-region arithmetic `45 = pairSum + 4 + 1`.  The complete and
    theorem-facing subtheorem indexes re-export these corollaries.

44. The exceptional canonical all-ones pair is now connected to the canonical
    upper case-bound branch.  `OEISBaseUpper.lean` lifts the already-proved
    OEIS facts that `(Q0,Q1)` is close and not intriguing through the canonical
    all-ones relabeling, in both orientations.  It proves
    `canonicalOneOneOneOne_zeroOne_caseBound_eq_five` and
    `canonicalOneOneOneOne_pairCross_le_caseBound_of_zeroOne`: whenever the
    canonical labels of an increasing pair are `0` and `1`, the automatic pair
    table value satisfies the exact canonical crossing-case bound.  This
    advances the upper side for the exceptional base branch only; the arbitrary
    close/intriguing route-savings obligations remain open.

45. A new additive theorem-facing folder now gives the requested statement /
    subtheorems / proof layout.  `TheoremOneAssembly/Statement.lean` states
    manuscript Theorem 1 as the displayed formula
    `a_Lop(n) = 4 * choose(n,2) + S(n) + n + 1`.
    `TheoremOneAssembly/Subtheorems.lean` records the proved generic theorem
    stack, the strongest current construction certificate boundary, the exact
    all-ones OEIS base table/arithmetic, and the exceptional/non-exceptional
    OEIS direction facts.  `TheoremOneAssembly/Proof.lean` proves
    `theorem_one` and `theorem_one_at` by assembling those subtheorems through
    the existing end-to-end certificate pipeline.  This folder is wired into
    `Lollipop.lean` and builds with the package.

46. The five non-exceptional exact OEIS base pairs are now formally classified
    as not close.  `CloseDirection.lean` adds
    `not_cyclicClosePair_of_abs_between` and its map-valued version.
    `KarlssonOEISGeometry.lean` proves the concrete normalized-direction
    inequalities for `(Q0,Q2)`, `(Q0,Q3)`, `(Q1,Q2)`, `(Q1,Q3)`, and
    `(Q2,Q3)`, using the `Q1` estimate
    `(1/100)/(2*pi) < 1/15`.  `OEISBaseUpper.lean` packages these as
    `base_not_cyclicClose_of_not_zeroOne`, lifts them through the canonical
    all-ones relabeling.  This completed the direction side of the
    non-exceptional branch before the strict Paulsen obtuse-distance
    inequalities below were added.

47. The exact all-ones OEIS base upper table is now unconditional.  The
    remaining strict Paulsen obtuse-distance inequalities for
    `(Q0,Q2)`, `(Q0,Q3)`, and `(Q2,Q3)` were proved in
    `CompleteFormalization/OEISPair02.lean`,
    `CompleteFormalization/OEISPair03.lean`, and
    `CompleteFormalization/OEISPair23.lean`, joining the existing `(Q1,Q2)`
    and `(Q1,Q3)` proofs.  `OEISBaseUpper.lean` lifts all six oriented
    distinct base-pair non-intriguing facts, proves
    `canonicalOneOneOneOne_not_circleIntriguing`,
    `canonicalOneOneOneOne_not_zeroOne_caseBound_eq_seven`, and
    `canonicalOneOneOneOne_pairCross_le_caseBound` for every increasing
    canonical all-ones pair.  `EndToEndFormalization/Subtheorems.lean`,
    `CompleteFormalization/Proof.lean`, and
    `TheoremOneAssembly/Subtheorems.lean` re-export these theorem-facing
    facts.  The exact all-ones OEIS base case now has the checked automatic
    lower table, checked upper case-bound comparison, pairwise equality with
    the Karlsson cluster table, and `40`/`45` arithmetic in Lean.

48. Section 5 has been re-audited against the actual Lean proof chain.  The
    matrix theorem endpoint is closed by named checked subtheorems:
    `isSupportStarForest_iff_canonicalShape`,
    `nonstar_support_has_descent_shape`, `support_descent_step_proven`,
    `support_compression_of_descent_step`,
    `canonicalStarForestMinimumCases_proven`, `starForestMinimum_proven`, and
    `matrix_theorem_proven`.  `TheoremOneAssembly/Subtheorems.lean` now
    re-exports these Section 5 endpoints in the theorem-facing
    statement/subtheorem/proof folder.  This confirms that the `3 x 4` matrix
    theorem is no longer a remaining assumption; the remaining end-to-end
    obligations are still the concrete model-specific construction fields
    listed in the bottom line.

49. The overlap-witness upper boundary has one more generic constructor.
    `EndToEndFormalization/OverlapUpper.lean` now proves
    `PairComponentAllFourOverlap.of_common_anchor`: when two primitive
    lollipops share their anchor, that point belongs to all four lifted
    circle/ray components.  `EndToEndFormalization/Subtheorems.lean` re-exports
    this as `common_anchor_to_all_four_overlap`, so common-anchor pairs can feed
    the existing direct whole-carrier `<= 4` savings theorem without a
    hand-built four-component witness.  The same file also proves
    `PairComponentFiveOverlap.of_all_four` and
    `PairComponentFiveOverlap.of_common_anchor`, re-exported as
    `all_four_overlap_to_five_overlap` and `common_anchor_to_five_overlap`,
    so the same all-four/common-anchor geometry feeds the close-only and
    intriguing-only `<= 5` overlap fields.  Finally,
    `pairCarrierSavingsFourOfCommonAnchor` and
    `pairCarrierSavingsFiveOfCommonAnchor` package the same common-anchor fact
    directly as `PairCarrierSavings` certificates under the usual
    noncoincidence hypotheses, and the theorem-facing index re-exports them as
    `common_anchor_to_direct_savings_four` and
    `common_anchor_to_direct_savings_five`.

50. The strongest theorem-facing construction boundary is now pinned down as
    `TheoremOneAssembly.ConstructionCertificate`, i.e.
    `EndToEndFormalization.StrongestCertificate`.  Its upper half is
    `OverlapUpper.OverlapSavingsStepwiseCertificate` and still needs, for
    every produced arrangement, the primitive arrangement, lifted-sphere and
    ray-supporting-line noncoincidence, close/intriguing/all-four overlap
    witnesses, radial-outward stems, and stepwise region increments for the
    automatic carrier table.  Its lower half is
    `AutomaticLower.StepwiseCanonicalKarlssonCarrierCardLowerCertificate` and
    still needs sorted blow-up arrangements, primitive arrangements,
    noncoincidence, agreement of the pair-crossing table with the automatic
    carrier table, automatic carrier-cardinality lower bounds for the
    canonical `4/5/7` table, and stepwise lower region increments.  Section 5,
    colored Zykov, weighted Turan, formula bridge, finite carrier construction
    from noncoincidence, OEIS all-ones base table, and common-anchor overlap
    savings are no longer the active blockers.

51. Added a separate construction-side lower bridge in
    `TheoremOneManuscript/ConstructionFormalization/LowerAnchorWitness.lean`.
    Lean now proves that if two primitive lollipops share their anchor, then
    that anchor lies in their primitive carrier intersection
    (`left_anchor_mem_pairIntersectionSet_of_common_anchor` and the
    arrangement-indexed version).  It also builds the resulting one-point
    finite lower subset (`common_anchor_lower_subset_one`) and proves that,
    once a local finite-carrier certificate is supplied, the corresponding
    pair-crossing entry is at least one
    (`one_le_pair_cross_of_common_anchor`).  The theorem-facing subtheorem
    index re-exports these as `common_anchor_mem_pair_intersection`,
    `common_anchor_to_lower_subset_one`, and
    `common_anchor_to_pair_cross_ge_one`.  This reduces one primitive lower
    geometry obligation, but it is still far short of the Nat-valued
    Karlsson `4/5/7` lower-cardinality bounds needed for arbitrary sorted
    blow-ups.

52. Added a reusable indexed lower-witness constructor in
    `TheoremOneManuscript/ConstructionFormalization/IndexedLowerWitness.lean`.
    If a construction supplies an injective family
    `points : Fin bound -> R2` and proves every indexed point lies in a given
    primitive pair carrier, Lean now builds
    `LocalPairCarrierLowerSubsetData ... bound` by taking
    `Finset.univ.image points`; the cardinality proof is discharged by
    `Finset.card_image_of_injective` and `Finset.card_fin`.  With a local
    finite-carrier certificate, Lean also derives the rational lower bound
    `(bound : Rat) <= pairCross i j`.  The theorem-facing subtheorem index
    re-exports these as `indexed_lower_subset_of_pair_intersections` and
    `indexed_points_to_pair_cross_lower_bound`.  This is the generic API
    needed for future concrete coordinate proofs of the `4`, `5`, and `7`
    lower multiplicities, but those coordinate point families themselves
    remain to be constructed for arbitrary sorted blow-ups.

53. Added `ConstructionFormalization/AutomaticCardinalityWitness.lean`, which
    targets the strongest current lower-bound field directly.  From an
    injective indexed family of primitive carrier-intersection points, Lean
    now proves a lower bound on
    `CompleteFormalization.FiniteCarrier.arrangementPairIntersectionFinset`
    using the automatic finset's exact `Set` specification and
    `Finset.card_le_card`.  It also derives the corresponding rational lower
    bound on `automaticCarrierCrossingTable`.  Shared-anchor pairs get the
    specialized one-point automatic-cardinality corollaries
    `one_le_arrangementPairIntersectionFinset_card_of_common_anchor` and
    `one_le_automaticCarrierCrossingTable_of_common_anchor`.  The
    theorem-facing subtheorem index re-exports these as
    `indexed_points_to_automatic_carrier_card_ge`,
    `indexed_points_to_automatic_pair_cross_lower_bound`,
    `common_anchor_to_automatic_carrier_card_ge_one`, and
    `common_anchor_to_automatic_pair_cross_ge_one`.  Future arbitrary blow-up
    work can now prove the canonical `4/5/7` automatic-cardinality field by
    giving distinct indexed carrier points; Lean handles the automatic-finset
    inclusion and card comparison.

54. The indexed lower-point bridge is now part of the theorem-facing
    end-to-end endpoint, not just a pointwise helper.  The new
    `StepwiseCanonicalKarlssonIndexedPointLowerCertificate` asks the lower
    construction for explicit indexed point families of size
    `canonicalKarlssonLowerSize q hq i j` for each canonical sorted-quad pair,
    plus injectivity and primitive carrier membership.  Lean converts this to
    `AutomaticLower.StepwiseCanonicalKarlssonCarrierCardLowerCertificate`.
    `EndToEndFormalization/Proof.lean` then defines
    `OverlapSavingsCanonicalKarlssonIndexedPointLowerCertificate` and proves
    `theorem_one_from_overlap_savings_canonical_karlsson_indexed_lower`, while
    `EndToEndFormalization/Statement.lean` exposes this as
    `IndexedPointCertificate` with theorem wrappers
    `theorem_one_from_indexed_points` and
    `theorem_one_at_from_indexed_points`.  The remaining lower work is now
    cleanly expressed as constructing those explicit point families and the
    ordered insertion-region data for arbitrary sorted blow-ups.

55. The indexed lower-point endpoint has also been lifted into the final
    theorem-facing `TheoremOneAssembly/` folder.  `Subtheorems.lean` now names
    `IndexedPointConstructionCertificate` and
    `IndexedPointTheoremOneSubtheorems`, while `Proof.lean` proves
    `theorem_one_from_indexed_points` and
    `theorem_one_at_from_indexed_points`.  This keeps the requested
    statement/subtheorems/proof organization intact while exposing the more
    concrete lower construction boundary at the same level as the main
    theorem assembly.

56. The complete-formalization index now exposes the same indexed lower-point
    theorem route.  `CompleteFormalization/Proof.lean` names
    `CompleteOverlapSavingsCanonicalKarlssonIndexedPointLowerCertificate` and
    proves
    `theorem_one_from_overlap_savings_canonical_karlsson_indexed_lower` plus
    its single-size version.  This keeps the complete index, the
    `EndToEndFormalization/` statement layer, and the final
    `TheoremOneAssembly/` folder aligned: the construction may either supply
    canonical automatic carrier-cardinality bounds directly or provide
    explicit indexed carrier-point families of the required canonical
    Nat-valued `4/5/7` sizes and let Lean perform the finite-set/cardinality
    conversion.

57. The manuscript's blow-up-stability proof text has been tightened at the
    main gap.  It now explicitly distinguishes ordinary persistence of
    transverse bounded component intersections from the unbounded ray
    components: new far-away ray intersections cannot be excluded by a bare
    compactness argument.  The proof text and the following Lean-status remark
    now say that the blow-up realization needs concrete coordinate/local
    perturbation certificates, equivalently local finite-carrier certificates,
    for every affected pair.  This matches the Lean boundary instead of
    overstating what has been formalized.

58. Added `ConstructionFormalization/IndexedCarrier.lean`, an exact indexed
    carrier bridge for future coordinate proofs.  If a construction supplies
    an injective indexed family `Fin k -> R2` whose image is exactly the
    primitive pair carrier, Lean now converts that enumeration into
    `LocalPairCarrierCrossingData` with crossing value `k`, derives the
    matching lower subset without a separate pointwise membership proof, and
    assembles exact indexed enumerations for all increasing pairs into
    `PairwiseCarrierCrossingData`.  `EndToEndFormalization/Subtheorems.lean`
    re-exports the bridge as `indexed_exact_carrier_to_local_pair_certificate`,
    `indexed_exact_carrier_to_lower_subset`, and
    `indexed_exact_carriers_to_pairwise_certificate`.  This reduces the
    remaining coordinate burden for arbitrary blow-ups to proving exact
    indexed carrier enumerations and the ordered insertion-region data.

59. Strengthened the exact indexed carrier bridge to the automatic finite
    carrier table.  From the same exact indexed carrier enumeration plus the
    standard noncoincident sphere/ray-line hypotheses, Lean now proves that
    `arrangementPairIntersectionFinset` has cardinality `k` and that
    `automaticCarrierCrossingTable` has value `(k : Rat)` for the pair.
    `EndToEndFormalization/Subtheorems.lean` re-exports these as
    `indexed_exact_carrier_to_automatic_carrier_card_eq` and
    `indexed_exact_carrier_to_automatic_pair_cross_eq`.  Thus an exact
    coordinate enumeration of a pair carrier feeds both the local
    finite-carrier certificate route and the strongest automatic-cardinality
    lower route.

60. Added a theorem-facing exact indexed-carrier lower certificate.  The new
    `StepwiseCanonicalKarlssonExactIndexedCarrierLowerCertificate` asks for
    exact indexed enumerations of the whole primitive pair carriers of the
    canonical Nat-valued `4/5/7` sizes, plus the simple pair-table facts on
    increasing and non-increasing entries.  Lean derives the older
    `StepwiseCanonicalKarlssonIndexedPointLowerCertificate` and then the
    canonical automatic-cardinality lower boundary.  This is lifted through
    `OverlapSavingsCanonicalKarlssonExactIndexedCarrierLowerCertificate`,
    `ExactIndexedCarrierCertificate`, the complete-formalization index, and
    `TheoremOneAssembly` as `theorem_one_from_exact_indexed_carriers`.  The
    remaining arbitrary blow-up lower task is now expressible as exact
    indexed carrier enumeration plus ordered insertion-region data, rather
    than as hand-built automatic cardinality inequalities.

61. Added a primitive coordinate-point constructor for upper overlap
    witnesses.  `OverlapUpper.lean` now proves that if one primitive point
    lies on both circles and both rays of a pair, then it gives
    `PairComponentAllFourOverlap`, `PairComponentFiveOverlap`, and direct
    `PairCarrierSavings ... 4`/`... 5` certificates under the standard
    noncoincident sphere/ray-line hypotheses.  `EndToEndFormalization/Subtheorems.lean`
    re-exports these as `primitive_point_to_all_four_overlap`,
    `primitive_point_to_five_overlap`,
    `primitive_point_to_direct_savings_four`, and
    `primitive_point_to_direct_savings_five`.  This reduces future
    coordinate-route work to proving ordinary primitive circle/ray membership
    for one point, rather than manually building lifted component-overlap
    witnesses.

62. Added a one-equation canonical-table variant of the exact indexed-carrier
    lower boundary.  `AutomaticCardinalityWitness.lean` now defines
    `canonicalKarlssonLowerTable`, proves its increasing entries are the
    canonical Nat-valued `4/5/7` sizes and its non-increasing entries are
    zero, and packages
    `StepwiseCanonicalKarlssonTableExactIndexedCarrierLowerCertificate`.
    This variant asks the future blow-up construction for exact indexed
    carrier enumerations plus a single equality between its pair table and
    the canonical rational lower table.  Lean derives the older
    increasing-entry/non-increasing-entry exact indexed-carrier certificate,
    then the indexed lower-point and automatic-cardinality boundaries.  The
    endpoint is lifted through `OverlapSavingsCanonicalKarlssonTableExactIndexedCarrierLowerCertificate`,
    `TableExactIndexedCarrierCertificate`, the complete-formalization index,
    and `TheoremOneAssembly` as
    `theorem_one_from_table_exact_indexed_carriers`.

63. Added primitive coordinate constructors for the upper two-double overlap
    route.  `OverlapUpper.lean` now has three constructors matching the three
    `PairComponentTwoDoubleOverlap` patterns: `cc/cr` with `rc/rr`,
    `cc/rc` with `cr/rr`, and `cc/rr` with `cr/rc`.  Each constructor takes
    ordinary primitive circle/ray membership facts for the named coordinate
    points and builds the lifted two-double witness; the file also supplies
    direct `PairCarrierSavings ... 5` wrappers under the usual noncoincident
    sphere/ray-line hypotheses.  `EndToEndFormalization/Subtheorems.lean`
    re-exports these as five-overlap and direct-savings bridge functions.
    This reduces future close/intriguing route certificates in the
    two-double case to concrete coordinate membership checks rather than
    manual lifted component-witness construction.

64. Re-exported the primitive upper-overlap route bridges at the theorem
    assembly layer.  `TheoremOneAssembly/Subtheorems.lean` now exposes the
    primitive all-four coordinate-point constructors and all three primitive
    two-double constructors, both as overlap witnesses and as direct
    `PairCarrierSavings` certificates.  This keeps the construction-facing
    upper route tools next to the Section 5 matrix endpoint and the final
    theorem-one assembly package.

65. Added monotonicity for direct whole-carrier savings.  `PairCarrierSavings`
    now has `mono`, which weakens any direct carrier bound to a larger bound,
    and `fourToFive`, which packages the common case where a `<= 4`
    certificate is used in a branch asking only for `<= 5`.
    `EndToEndFormalization/Subtheorems.lean` and
    `TheoremOneAssembly/Subtheorems.lean` re-export these as
    `direct_carrier_savings_mono` and
    `direct_carrier_savings_four_to_five`.  Future route proofs can therefore
    provide the strongest available coupled carrier bound once and reuse it
    across weaker upper branches without duplicating route constructors.

66. Added a family-level primitive-coordinate overlap upper boundary.
    `EndToEndFormalization/OverlapUpper.lean` now defines
    `PrimitivePairAllFourOverlap`, `PrimitivePairFiveOverlap`, and
    `PrimitiveOverlapSavingsStepwiseCertificate`.  These packages ask for raw
    primitive circle/ray membership facts in the close, intriguing, and
    close-intriguing branches; Lean converts them to the existing lifted
    overlap upper certificate and then to direct whole-carrier savings.
    `EndToEndFormalization/Proof.lean`, `Statement.lean`,
    `Subtheorems.lean`, `CompleteFormalization/Proof.lean`, and
    `TheoremOneAssembly/` now expose the combined primitive-upper plus
    one-equation table-exact lower endpoint, with theorem names including
    `theorem_one_from_primitive_table_exact_indexed_carriers` and the longer
    `theorem_one_from_primitive_overlap_savings_canonical_karlsson_table_exact_indexed_carrier_lower`.
    This removes another layer of lifted-overlap bookkeeping from future
    coordinate constructions, but it still leaves the real geometric task:
    prove the required coordinate membership facts for arbitrary close and
    intriguing pairs in the intended blow-ups.

67. Reduced exact indexed-carrier bookkeeping to membership and coverage
    checks.  `PrimitiveGeometry/Basic.lean` now proves that primitive
    pair-carrier membership is equivalent to the four circle/ray component
    cases: circle-circle, circle-ray, ray-circle, and ray-ray.  It also
    exposes direct membership constructors for each case.  `ConstructionFormalization/IndexedCarrier.lean`
    now proves that the exact image equality required by indexed carrier
    certificates follows from two simpler fields: every indexed point lies in
    the pair carrier, and every pair-carrier point is hit by some index.  A
    component-wise variant lets future coordinate proofs cover the four
    circle/ray cases separately.  The new helpers also build the corresponding
    `LocalPairCarrierCrossingData` and lower-subset certificates from
    membership/coverage data.  `EndToEndFormalization/Subtheorems.lean` and
    `TheoremOneAssembly/Subtheorems.lean` re-export these helpers.  This does
    not enumerate any new arbitrary blow-up carrier by itself, but it changes
    the future exact-carrier proof obligation from a raw set equality into
    ordinary point membership plus exhaustive component coverage.

68. Added a finset-exact carrier lower boundary.  `ConstructionFormalization/AutomaticCardinalityWitness.lean`
    now defines
    `StepwiseCanonicalKarlssonFinsetExactCarrierLowerCertificate`, where the
    construction supplies, for each increasing canonical pair, the exact
    finite carrier set, the set equality with the automatic carrier finset,
    and the exact Nat-valued Karlsson cardinality.  Lean converts this
    directly to `StepwiseCanonicalKarlssonCarrierCardLowerCertificate`, so
    the lower theorem stack can use the automatic carrier finset as the
    cardinality witness.  `EndToEndFormalization/Proof.lean`,
    `Statement.lean`, `Subtheorems.lean`, `CompleteFormalization/Proof.lean`,
    and `TheoremOneAssembly/` now expose theorem endpoints from these
    finset-exact lower certificates, including
    `theorem_one_from_finset_exact_carriers`,
    `theorem_one_from_primitive_finset_exact_carriers`, and the longer
    `theorem_one_from_overlap_savings_canonical_karlsson_finset_exact_carrier_lower`
    variants.  This avoids forcing future coordinate constructions to
    manufacture indexed enumerations when an exact finite carrier set plus a
    set equality and cardinality proof is more natural.  It still does not
    produce the arbitrary sorted Karlsson blow-up carrier sets by itself.

69. Reduced the finset-exact carrier equality obligation to coverage checks.
    `ConstructionFormalization/IndexedCarrier.lean` now proves
    `carrierFinset_spec_of_mem_and_cover` and
    `carrierFinset_spec_of_component_covers`: an exact finite carrier set can
    be identified with a primitive pair carrier by proving that every listed
    point lies in the carrier and every carrier point is listed, or by
    covering the four circle/ray component cases separately.  The same file
    proves that such an exact finite set is equal to Lean's automatic carrier
    finset and computes the automatic carrier cardinality and crossing-table
    entry.  `EndToEndFormalization/Subtheorems.lean` and
    `TheoremOneAssembly/Subtheorems.lean` re-export the new helper names.
    This makes the finset-exact lower endpoint match the natural shape of a
    future coordinate proof: build a finite set, prove membership and
    exhaustive component coverage, compute its cardinality.

70. Promoted component-covered finite carriers to a full theorem endpoint.
    `ConstructionFormalization/AutomaticCardinalityWitness.lean` now defines
    `StepwiseCanonicalKarlssonComponentCoveredFinsetLowerCertificate`: for
    every increasing canonical pair, the lower construction supplies a finite
    carrier set, proves every listed point is in the pair carrier, proves
    coverage of each circle-circle/circle-ray/ray-circle/ray-ray component,
    computes the Nat-valued Karlsson cardinality, and supplies the stepwise
    region recurrence.  Lean derives the exact finite-carrier equality and
    converts this to the existing finset-exact and automatic-cardinality
    lower boundaries.  `EndToEndFormalization/Proof.lean`,
    `Statement.lean`, `Subtheorems.lean`, `CompleteFormalization/Proof.lean`,
    and `TheoremOneAssembly/` now expose theorem endpoints from these
    component-covered finite-carrier certificates, including
    `theorem_one_from_component_covered_finsets`,
    `theorem_one_from_primitive_component_covered_finsets`, and the longer
    `theorem_one_from_overlap_savings_canonical_karlsson_component_covered_finset_lower`
    variants.  This is still not the arbitrary sorted blow-up construction,
    but it removes the raw set-equality field from the strongest lower
    theorem-facing certificate.

71. Added a component-separated finite-carrier lower endpoint.
    `ConstructionFormalization/IndexedCarrier.lean` now defines
    `componentCarrierFinset`, the union of four finite component sets, and
    proves that per-component membership plus per-component coverage identifies
    this union with the whole primitive pair carrier.  `AutomaticCardinalityWitness.lean`
    now defines
    `StepwiseCanonicalKarlssonComponentFinsetLowerCertificate`: for every
    increasing canonical pair, the lower construction supplies separate
    circle-circle, circle-ray, ray-circle, and ray-ray finite sets, proves
    membership and coverage for each component, computes the cardinality of
    their union, and supplies the stepwise region recurrence.  Lean converts
    this to the component-covered, finset-exact, and automatic-cardinality
    lower boundaries.  `EndToEndFormalization/Proof.lean`, `Statement.lean`,
    `Subtheorems.lean`, `CompleteFormalization/Proof.lean`, and
    `TheoremOneAssembly/` expose theorem endpoints including
    `theorem_one_from_component_finsets`,
    `theorem_one_from_primitive_component_finsets`, and the longer
    `theorem_one_from_overlap_savings_canonical_karlsson_component_finset_lower`
    variants.  This matches the shape of the already proved OEIS seven-point
    component witnesses, while still leaving the arbitrary sorted blow-up
    coordinates and cardinality calculation as real construction work.

72. Added a disjoint component-count lower endpoint.  `IndexedCarrier.lean`
    now proves `componentCarrierFinset_card_eq_of_disjoint`: if the four
    component finsets are pairwise disjoint and their individual cardinalities
    are known, then the cardinality of their union is the sum of those four
    cardinalities.  `AutomaticCardinalityWitness.lean` now defines
    `StepwiseCanonicalKarlssonDisjointComponentFinsetLowerCertificate`, where
    each increasing canonical pair supplies the four component finsets,
    membership and coverage for the four circle/ray component cases, the six
    pairwise-disjointness proofs, four component cardinalities, and one
    component-size sum equal to the canonical Nat-valued Karlsson lower size.
    Lean converts this to the component-finset, component-covered,
    finset-exact, and automatic-cardinality lower boundaries.  The
    end-to-end, complete, and theorem-assembly layers expose
    `theorem_one_from_disjoint_component_finsets`,
    `theorem_one_from_primitive_disjoint_component_finsets`, and the longer
    overlap-witness disjoint component-finset endpoints.  This removes another
    bookkeeping burden from future coordinate proofs, but it still does not
    construct the arbitrary sorted Karlsson blow-up coordinates or prove their
    route-savings obligations.

73. Added an indexed disjoint component-count endpoint.  The new
    `StepwiseCanonicalKarlssonIndexedDisjointComponentFinsetLowerCertificate`
    lets a future coordinate proof give each circle-circle, circle-ray,
    ray-circle, and ray-ray component as an injective indexed point family
    rather than as a prebuilt `Finset`.  It supplies component membership,
    component coverage, pairwise disjointness of the four indexed images, and
    the component-size sum.  Lean builds the four component finsets with
    `indexedCarrierFinset`, proves their cardinalities from injectivity, and
    converts the package to the disjoint component-finset boundary and hence
    to the automatic-cardinality lower theorem stack.  The theorem-facing
    layers expose `theorem_one_from_indexed_disjoint_component_finsets` and
    `theorem_one_from_primitive_indexed_disjoint_component_finsets`.  This is
    now the most coordinate-facing lower endpoint: the remaining lower proof
    can be stated as four explicit indexed point families per pair, coverage,
    disjointness, and ordered insertion-region data.  It is still not the
    construction of those point families for arbitrary sorted Karlsson
    blow-ups.

74. Added a lower-bound-only component-indexed endpoint.  The exact
    component-finset endpoints are stronger than necessary for the lower
    inequality because they ask for coverage of the whole primitive carrier.
    `AutomaticCardinalityWitness.lean` now defines
    `StepwiseCanonicalKarlssonComponentIndexedPointLowerCertificate`, where a
    construction supplies four indexed component point families, injectivity
    within each family, component membership, pairwise disjointness of the four
    images, and a component-size sum equal to the canonical Nat-valued
    Karlsson lower size.  Lean unions the four images, proves the union has
    the canonical cardinality, noncomputably enumerates that finite union by
    `Fin (canonicalKarlssonLowerSize ...)`, and converts it to the existing
    indexed lower-point boundary.  The end-to-end, complete, and assembly
    layers expose `theorem_one_from_component_indexed_points` and
    `theorem_one_from_primitive_component_indexed_points`.  This is now the
    natural lower-bound endpoint for future blow-up coordinate proofs: enough
    distinct component points suffice; exact carrier coverage is only needed
    for exact crossing-table certificates.

75. Strengthened the triple-overlap upper route.  In
    `PrimitiveGeometry/OverlapSavings.lean`, Lean now proves
    `pairComponentTripleOverlap_all_four`: because the four carrier
    components are product components (`circle-circle`, `circle-ray`,
    `ray-circle`, `ray-ray`), a single lifted point lying in any three of
    them automatically lies in the fourth.  The same file packages this as
    `finset_card_le_four_of_triple_component_overlap` and
    `pairCarrierSavingsFourOfTripleComponentOverlap`, so a triple-overlap
    witness gives direct whole-carrier `<= 4` savings, not only the earlier
    `<= 5` bound.  `EndToEndFormalization/OverlapUpper.lean`,
    `EndToEndFormalization/Subtheorems.lean`, and
    `TheoremOneAssembly/Subtheorems.lean` expose theorem-facing aliases
    including `triple_overlap_forces_all_four_components` and
    `triple_overlap_to_direct_savings_four`.  This does not remove the need
    for the construction to prove close/intriguing overlap or route
    witnesses, but it tightens the checked upper endpoint when a triple
    witness is available.

76. Strengthened the coincident two-double overlap route.  The two-double
    overlap theorem already allowed the two witnesses to coincide, but it
    only used that data for the weaker `<= 5` bound.  Lean now proves
    `pairComponentTwoDoubleOverlap_all_four_of_same_point`: a
    two-double-overlap certificate of type
    `PairComponentTwoDoubleOverlap L M q q` gives membership of `q` in all
    four lifted circle/ray components.  This is packaged as
    `finset_card_le_four_of_two_double_component_overlap_same_point` and
    `pairCarrierSavingsFourOfTwoDoubleComponentOverlapSamePoint`, and the
    end-to-end and assembly subtheorem indexes expose
    `two_double_same_point_overlap_forces_all_four_components` and
    `two_double_same_point_overlap_to_direct_savings_four`.  Thus the
    overlap upper API now distinguishes genuine two-point two-double `<= 5`
    data from coincident two-double data, which is really an all-four
    `<= 4` route.

77. Exposed named route transport through the end-to-end and theorem-facing
    subtheorem indexes.  `EndToEndFormalization/Subtheorems.lean` and
    `TheoremOneAssembly/Subtheorems.lean` now name the generic conversions
    from `PairComponentSavings` to `PairCarrierSavings`, from generic
    noncoincident circle/ray-line data to the `<= 7` component/direct savings
    certificates, from `PairComponentSavingsFiveRoute` and
    `PairComponentSavingsFourRoute` to both component-savings and direct
    whole-carrier savings certificates, and from either component-savings or
    direct whole-carrier savings to local/global rational crossing-table
    bounds.  This does not prove the missing arbitrary close/intriguing
    geometric route constructors, but it removes another presentation layer:
    future construction work can cite the named first-principles route
    constructors and Lean-facing crossing-bound transport directly.

78. Added a raw primitive triple-overlap certificate boundary.  The new
    `PrimitivePairTripleOverlap` type in
    `EndToEndFormalization/OverlapUpper.lean` accepts ordinary coordinate
    circle/ray membership facts showing that one primitive point lies in any
    three of the four product components.  Lean converts that data to
    `PrimitivePairAllFourOverlap`, to the lifted
    `PairComponentAllFourOverlap`, to `PrimitivePairFiveOverlap`, and to
    direct whole-carrier `PairCarrierSavings` certificates with bounds `4`
    and `5` under the standard noncoincident-sphere and noncoincident-ray-line
    hypotheses.  The end-to-end and theorem-facing subtheorem indexes expose
    the new aliases
    `primitive_triple_overlap_to_all_four_overlap`,
    `primitive_triple_overlap_to_primitive_five_overlap`,
    `primitive_triple_overlap_to_direct_savings_four`, and
    `primitive_triple_overlap_to_direct_savings_five`.  This closes another
    presentation gap between raw coordinate witnesses and the overlap upper
    theorem boundary, but it still does not produce the arbitrary
    close/intriguing route witnesses or the concrete sorted Karlsson blow-up
    lower data.

79. Added primitive same-point two-double bridges to the stronger overlap
    route.  The abstract same-point two-double theorem was already proved, but
    raw primitive coordinate witnesses only exposed the ordinary two-point
    `<= 5` constructors.  `EndToEndFormalization/OverlapUpper.lean` now has
    primitive same-point constructors for all three two-double patterns:
    `cc/cr` with `rc/rr`, `cc/rc` with `cr/rr`, and `cc/rr` with `cr/rc`.
    Each converts ordinary circle/ray membership facts for one coordinate
    point into a lifted all-four overlap witness and a direct whole-carrier
    `PairCarrierSavings ... 4` certificate under the standard noncoincident
    sphere and ray-line hypotheses.  The end-to-end and theorem-facing
    subtheorem indexes expose the corresponding all-four-overlap and direct
    `<= 4` aliases.  This is another bookkeeping reduction for future raw
    coordinate route certificates, not a proof of the remaining arbitrary
    close/intriguing route constructors.

80. Added a flexible primitive `<= 4` upper boundary.  `OverlapUpper.lean` now
    defines `PrimitivePairFourOverlap`, which bundles raw all-four data, raw
    primitive triple-overlap data, and all three primitive same-point
    two-double patterns.  Lean converts this type to
    `PrimitivePairAllFourOverlap`, the lifted all-four component witness, the
    primitive five-overlap witness, and direct whole-carrier
    `PairCarrierSavings ... 4`.  The new
    `PrimitiveFlexibleOverlapSavingsStepwiseCertificate` lets the
    close-and-intriguing branch of a family-level primitive upper certificate
    use any of these primitive `<= 4` witnesses, then converts back to the
    existing primitive-overlap upper boundary.  The end-to-end statement layer
    now has a direct theorem endpoint
    `theorem_one_from_primitive_flexible_component_indexed_points`, and the
    theorem-facing assembly layer mirrors it.  This is still a certificate
    boundary: the construction must still supply the raw coordinate witnesses
    and the lower component-indexed point families.

81. Expanded the flexible primitive upper boundary across the existing
    primitive lower endpoints.  The first flexible endpoint only paired
    `PrimitiveFlexibleOverlapSavingsStepwiseCertificate` with the
    component-indexed lower-point boundary.  `EndToEndFormalization/Proof.lean`
    now also has flexible versions of the primitive table-exact indexed-carrier,
    finset-exact carrier, component-covered finite-carrier, component-finset,
    disjoint component-finset, and indexed disjoint component-finset theorem
    certificates.  `Statement.lean` and `TheoremOneAssembly/` expose matching
    theorem-facing aliases and theorem endpoints.  This is a purely
    first-principles transport reduction: it lets any of the current
    construction-side lower formats use the wider primitive `<= 4` upper input,
    but it still relies on the construction to provide the raw coordinate upper
    witnesses and the corresponding lower carrier data.

82. Added the missing primitive/flexible canonical automatic-cardinality
    endpoint.  The flexible primitive upper boundary had already been threaded
    through the concrete lower formats, but the simplest canonical-cardinality
    boundary still only exposed overlap-witness upper data.  `Proof.lean` now
    has `PrimitiveOverlapSavingsCanonicalKarlssonCardLowerCertificate`,
    `PrimitiveFlexibleOverlapSavingsCanonicalKarlssonCardLowerCertificate`,
    and theorem endpoints
    `theorem_one_from_primitive_overlap_savings_canonical_karlsson_card_lower`
    and
    `theorem_one_from_primitive_flexible_overlap_savings_canonical_karlsson_card_lower`
    with single-size variants.  `Statement.lean` exposes the shorter
    `theorem_one_from_primitive_canonical_card_bounds` and
    `theorem_one_from_primitive_flexible_canonical_card_bounds` endpoints, and
    `TheoremOneAssembly/` mirrors them as theorem-facing subtheorem packages.
    This is still a transport result: it lets future coordinate witnesses use
    the flexible primitive `<= 4` upper input together with direct canonical
    automatic carrier-cardinality lower bounds.

83. Mirrored the flexible primitive endpoints into the broad
    `CompleteFormalization/Proof.lean` index.  That index previously named the
    older primitive lower-bound formats but not the flexible primitive
    variants.  It now exposes complete-index aliases and theorem endpoints for
    primitive and flexible canonical automatic-cardinality lower data, plus
    flexible primitive component-indexed, table-exact indexed-carrier,
    finset-exact, component-covered, component-finset, disjoint
    component-finset, and indexed disjoint component-finset lower data.  This
    keeps the broad theorem-one index in sync with the cleaner
    `EndToEndFormalization/Statement.lean` and `TheoremOneAssembly/` surfaces.

84. Exposed the primitive/flexible canonical automatic-cardinality endpoint in
    the theorem-facing split boundary.  `StatementProof/Boundary.lean` now
    names `PrimitiveOverlapUpperData`, `PrimitiveFlexibleOverlapUpperData`, and
    `CanonicalCarrierCardLowerData`, plus split construction packages
    `PrimitiveCanonicalCardConstructionData` and
    `PrimitiveFlexibleCanonicalCardConstructionData`.  Each package converts to
    the corresponding complete-index certificate and proves `theorem_one`,
    `theorem_one_at`, and the unfolded displayed formula.  This makes the
    clean statement/proof boundary expose the same coordinate-overlap plus
    canonical automatic-cardinality route that the lower-level end-to-end
    files already proved.

85. Added direct statement/proof aliases for the primitive/flexible canonical
    automatic-cardinality endpoint.  `StatementProof/Statement.lean` now names
    `PrimitiveCanonicalCardModelData` and
    `PrimitiveFlexibleCanonicalCardModelData` as alternate sufficient
    model-data boundaries for the same displayed Theorem 1 statement.
    `StatementProof/Proof.lean` proves theorem, single-size, and unfolded
    displayed-form wrappers from both aliases.  The compact `ModelData`
    endpoint remains unchanged; these aliases make the newer primitive
    coordinate-overlap boundary visible from the clean theorem-facing folder.

86. Added primitive/flexible canonical automatic-cardinality aliases to the
    clean subtheorem index.  `StatementProof/Subtheorems.lean` now records
    named theorem aliases showing that `PrimitiveCanonicalCardModelData` and
    `PrimitiveFlexibleCanonicalCardModelData` imply the displayed Theorem 1
    statement and each single-size formula.  This keeps the "statement,
    subtheorems, proof" folder aligned with the newer construction boundary.

87. Mirrored the remaining common-anchor and primitive direct-overlap bridges
    through the theorem-facing assembly layer.  `TheoremOneAssembly/Subtheorems.lean`
    now exposes the common-anchor all-four/five overlap witnesses, the
    common-anchor direct `<= 4` and `<= 5` carrier-savings certificates, the
    all-four-to-five weakening, and the raw primitive all-four/five direct
    savings aliases.  `StatementProof/Subtheorems.lean` also exposes the
    common-anchor and primitive all-four/five direct savings bridge names.
    These are transport/exposure facts, not new construction assumptions:
    they forward existing checked `EndToEndFormalization` proofs.

88. Added a clean lower-bridge index for the final statement/proof folder.
    `StatementProof/LowerBridges.lean` re-exports the proved end-to-end lower
    reductions: exact indexed carriers, exact finite carriers, indexed lower
    subsets, common-anchor singleton lower witnesses, automatic carrier-table
    cardinality facts, the canonical sorted Karlsson lower table, and every
    conversion from component/finset/indexed-disjoint lower formats to the
    canonical automatic carrier-cardinality and monotone local lower
    boundaries.  `StatementProof/Subtheorems.lean` imports this file, so the
    clean theorem-facing folder now exposes both the primitive/flexible upper
    bridge and the canonical lower bridge stack.

89. Added the matching clean upper-bridge index.  `StatementProof/UpperBridges.lean`
    re-exports the proved route/direct-savings/overlap upper transport lemmas:
    direct-savings symmetry and monotonicity, component-to-direct savings,
    generic noncoincident `<= 7` savings, five/four route conversion to
    component and direct savings, local/global pair-crossing bounds from
    savings, five/all-four overlap to direct savings, triple and same-point
    two-double all-four/direct bridges, primitive point/triple/four/two-double
    upper constructors, and the overlap-upper certificate conversions.  The
    common-anchor and primitive all-four/five direct aliases remain stated
    explicitly in `StatementProof/Subtheorems.lean` with local docstrings.

90. Exposed the most coordinate-facing lower construction format through the
    clean split boundary.  `StatementProof/Boundary.lean` now names
    `OverlapUpperData` and
    `CanonicalIndexedDisjointComponentFinsetLowerData`, then packages
    `IndexedDisjointComponentFinsetConstructionData`,
    `PrimitiveIndexedDisjointComponentFinsetConstructionData`, and
    `PrimitiveFlexibleIndexedDisjointComponentFinsetConstructionData`.  Each
    package converts to the corresponding complete certificate and proves
    `theorem_one`, `theorem_one_at`, and the unfolded displayed formula.  This
    means the final clean boundary can now be fed by overlap or raw primitive
    upper witnesses plus injective indexed point families for the four
    disjoint lower carrier components, without going through the broader
    `CompleteFormalization` index manually.

91. Added the lower-bound-only component-indexed split boundary next to the
    indexed-disjoint exact-carrier boundary.  `StatementProof/Boundary.lean`
    now also names `CanonicalComponentIndexedPointLowerData` and packages
    `ComponentIndexedPointConstructionData`,
    `PrimitiveComponentIndexedPointConstructionData`, and
    `PrimitiveFlexibleComponentIndexedPointConstructionData`.  These endpoints
    prove the theorem and unfolded formula from overlap/primitive/flexible
    primitive upper witnesses plus four disjoint component point families whose
    union has the canonical `4/5/7` size, without requiring exact coverage of
    the whole primitive carrier.

92. Added a clean theorem-endpoint index for the final statement/proof folder.
    `StatementProof/EndpointTheorems.lean` re-exports every proved
    complete-formalization theorem-one endpoint under the `StatementProof`
    namespace, except the base `theorem_one` and `theorem_one_at` wrappers
    already documented in `StatementProof/Proof.lean`.  This makes the
    monotone-lower, direct-savings, automatic-lower, overlap, primitive,
    flexible primitive, component-indexed, exact-carrier, table-exact,
    finset-exact, component-covered, component-finset, disjoint-component, and
    indexed-disjoint-component theorem endpoints available from the clean
    theorem-facing import path.

## Bottom Line

Subject to the remaining close/intriguing route-savings input for the
primitive lollipop carriers, plus concrete coordinate/local perturbation data
giving automatic carrier finset cardinality lower bounds of the Nat-valued
Karlsson `4/5/7` sizes for Lean's canonical sorted-quad cluster labels in
arbitrary sorted blow-ups and ordered insertion-region data, I currently think
the manuscript gives a genuine proof
of the stated formula.  The newly formalized normalized-bearing bridge removes
one ambiguity in the close-direction input, the checked non-exceptional OEIS
direction inequalities and strict Paulsen obtuse-distance inequalities remove
the close/non-intriguing classification gaps in the exact all-ones base, the
checked close-route audit
rules out one invalid shortcut, the direct-overlap theorems prove real
`<= 5` and `<= 4` savings bounds from two double-overlaps and all-four
component overlap, additionally prove that triple overlap and coincident
two-double overlap force all-four overlap and hence give the stronger
`<= 4` bound, and now feed a concrete overlap-witness automatic upper
boundary, with primitive all-four point, raw primitive triple-overlap, and
two-double point constructors, including same-point two-double constructors
for direct `<= 4` savings, a flexible primitive `<= 4` overlap upper boundary,
now threaded through all current primitive lower endpoint formats including
the canonical automatic-cardinality endpoint, a
family-level primitive-coordinate upper certificate, and
monotone direct-savings weakening for future coordinate witnesses; the named
route constructors are now also exposed through theorem-facing transport
lemmas to component/direct savings and local/global crossing-table bounds,
and the
new automatic lower endpoint shows finite
carrier-subset witnesses or automatic carrier-cardinality witnesses of the
required `4/5/7` sizes are enough for the lower construction and, in the
headline statement, the cluster witness is canonical rather than an extra
input.  The exact OEIS four-base automatic table is now proved in the
canonical all-ones case, both below and above, but arbitrary route-savings and
concrete blow-up realization data remain genuine construction obligations;
the indexed lower-witness, exact indexed-carrier-to-automatic-table, and
automatic-cardinality APIs, now including the one-equation canonical-table
exact-carrier variant, the finset-exact carrier variant, and their
component-covered refinements and primitive-coordinate upper endpoints, reduce the future
finite-carrier/cardinality bookkeeping; the new exact-carrier
membership/coverage helpers reduce the indexed set-equality proofs to
component-wise coverage checks, while the finset-exact endpoint and its new
coverage helpers remove the need to introduce indexed enumerations when a
finite carrier set is already available; the component-covered theorem
endpoint now makes membership plus four component-coverage fields sufficient
as the advertised lower certificate, and the component-finset endpoint lets
the construction provide the four component finite sets directly; the
disjoint component-finset endpoint also lets Lean derive the union
cardinality from pairwise disjointness and four component counts; the indexed
disjoint component-finset endpoint further replaces those component finsets
by injective indexed point families; and the component-indexed lower-point
endpoint removes the exact carrier-coverage burden when only the lower
inequality is needed.  The
common-anchor singleton lower bridge only proves an unavoidable first
intersection point, not the required `4/5/7` multiplicities.  I
did not find a hole in the colored
Turan/blocker/matrix argument.

The strongest negative finding is about presentation/formalization, not the mathematics: the Lean files should not be described as a full formal proof of the theorem, and the package needs reproducibility fixes.
