import Lollipop.Internal.ColoredTuran.Proof
import Lollipop.Internal.ColoredTuran.ColoredQuotientCertificates
import Lollipop.Internal.ColoredTuran.GeometricReduction
import Lollipop.Internal.ColoredTuran.GeometricPaulsenReduction
import Lollipop.Internal.ColoredTuran.WeightedTuranCertificates

/-!
Final Theorem 1 endpoint.

This folder is intentionally small and non-disruptive.  It packages the
existing formalization in the mathlib style used for maximum theorems:
`IsGreatest (Set.range ...) value`.  That statement simultaneously records
attainment and the universal upper bound.

The generic combinatorial and algebraic subtheorems imported here are proved
in the `Lollipop` tree.  The only remaining inputs are the model-specific
certificate producers for the concrete lollipop family: refined upper
certificates for every arrangement and lower realizations.
-/

namespace Lollipop
namespace TheoremOneFinal

universe u

/-- Theorem 1 as a mathlib-style maximum statement for an abstract lollipop
problem family. -/
def TheoremOneStatement (P : TheoremOne.ProblemFamily.{u}) : Prop :=
  TheoremOne.MaximumStatement P

/-- Theorem 1 as the displayed formula for a family with a named maximum
function. -/
def TheoremOneFormulaStatement (P : TheoremOne.MaxProblemFamily.{u}) : Prop :=
  TheoremOne.FormulaStatement P

/-- The remaining model-specific subtheorems after the generic proof has been
formalized.  These are certificate-production statements rather than algebraic
or matrix inequalities: every arrangement supplies the refined pairwise upper
certificate, and every size has a lower realization attaining the candidate
value. -/
structure ModelSubtheorems (P : TheoremOne.ProblemFamily.{u}) : Prop where
  upper_certificates : TheoremOneEndToEnd.PairwisePartitionMatrixUpperCertificates P
  lower_realizations : TheoremOne.LowerRealizations P

/-- Stronger model-specific subtheorems after the weighted Turan theorem has
been internalized.  Upper certificates now supply actual blocker graphs whose
off-diagonal complements are clique-free; Lean generates the Turan partitions
and then runs the partition-intersection/matrix pipeline. -/
structure WeightedTuranModelSubtheorems
    (P : TheoremOne.ProblemFamily.{u}) : Prop where
  upper_certificates : TheoremOneEndToEnd.PairwiseWeightedTuranUpperCertificates P
  lower_realizations : TheoremOne.LowerRealizations P

/-- Strongest currently internalized upper-certificate package.  Upper
certificates supply no-zero colored quotient certificates.  Lean then derives
the blocker complement clique-free hypotheses, chooses the weighted-Turan
partitions, runs the partition-intersection/matrix pipeline, and applies the
pairwise lollipop reduction. -/
structure ColoredQuotientModelSubtheorems
    (P : TheoremOne.ProblemFamily.{u}) : Prop where
  upper_certificates :
    TheoremOneEndToEnd.PairwiseColoredQuotientUpperCertificates P
  lower_realizations : TheoremOne.LowerRealizations P

/-- Strongest internalized upper-certificate package.  Upper certificates
provide only the original colored graph for the two-graph reduction, with the
`D`/`E` forbidden-clique hypotheses and the geometric pairwise score bounds.
Lean then performs colored Zykov, quotienting, weighted Turan,
partition-intersection, Section 5, and pairwise summation internally. -/
structure ColoredGraphModelSubtheorems
    (P : TheoremOne.ProblemFamily.{u}) : Prop where
  upper_certificates :
    TheoremOneEndToEnd.PairwiseColoredGraphUpperCertificates P
  lower_realizations : TheoremOne.LowerRealizations P

/-- Strongest upper-bound interface before choosing an explicit Euclidean
coordinate model.  Upper certificates provide the manuscript's close and
intriguing predicates, pairwise crossing table, geometric crossing cases, and
the two finite forbidden-pair facts.  Lean constructs the colored graph and
then performs colored Zykov, quotienting, weighted Turan,
partition-intersection, Section 5, and pairwise summation internally. -/
structure GeometricModelSubtheorems
    (P : TheoremOne.ProblemFamily.{u}) : Prop where
  upper_certificates :
    TheoremOneEndToEnd.PairwiseGeometricUpperCertificates P
  lower_realizations : TheoremOne.LowerRealizations P

/-- Geometric model package with Paulsen's five-circle linear algebra
internalized.  The upper certificates still supply the pairwise crossing
geometry and the close-pair-in-four fact, but the five-intriguing-pair fact is
derived in Lean from Paulsen vector witnesses on every five-element subset. -/
structure PaulsenGeometricModelSubtheorems
    (P : TheoremOne.ProblemFamily.{u}) : Prop where
  upper_certificates :
    TheoremOneEndToEnd.PairwisePaulsenGeometricUpperCertificates P
  lower_realizations : TheoremOne.LowerRealizations P

/-- Geometric model package with Paulsen's appendix reduced to circle
coordinates and distance inequalities.  Lean constructs Paulsen vectors,
proves their Gram inequalities, derives the five-intriguing-pair fact, and
then runs the rest of the upper-bound stack internally. -/
structure PaulsenCircleGeometricModelSubtheorems
    (P : TheoremOne.ProblemFamily.{u}) : Prop where
  upper_certificates :
    TheoremOneEndToEnd.PairwisePaulsenCircleGeometricUpperCertificates P
  lower_realizations : TheoremOne.LowerRealizations P

/-- Geometric model package with one global circle-coordinate model per
arrangement.  Lean restricts the global centers/radii to every five-subset,
builds the Paulsen circle data, derives the five-intriguing-pair fact, and
then runs the rest of the upper-bound stack internally. -/
structure GlobalCircleGeometricModelSubtheorems
    (P : TheoremOne.ProblemFamily.{u}) : Prop where
  upper_certificates :
    TheoremOneEndToEnd.PairwiseGlobalCircleGeometricUpperCertificates P
  lower_realizations : TheoremOne.LowerRealizations P

/-- Geometric model package with one global circle-coordinate model per
arrangement and with `intriguing` fixed to the canonical Paulsen circle
relation. -/
structure CanonicalCircleGeometricModelSubtheorems
    (P : TheoremOne.ProblemFamily.{u}) : Prop where
  upper_certificates :
    TheoremOneEndToEnd.PairwiseCanonicalCircleGeometricUpperCertificates P
  lower_realizations : TheoremOne.LowerRealizations P

/-- Strongest current geometric upper model.  The close relation is fixed to
the canonical cyclic direction relation and the intriguing relation is fixed to
the canonical Paulsen circle relation; Lean derives both finite
forbidden-pair facts. -/
structure CanonicalGeometricModelSubtheorems
    (P : TheoremOne.ProblemFamily.{u}) : Prop where
  upper_certificates :
    TheoremOneEndToEnd.PairwiseCanonicalGeometricUpperCertificates P
  lower_realizations : TheoremOne.LowerRealizations P

/-- Strongest current concise geometric upper model.  The close and
intriguing relations are canonical, and the pairwise crossing estimate is
supplied as one four-case table; Lean expands that table and derives both
finite forbidden-pair facts. -/
structure CanonicalCaseBoundGeometricModelSubtheorems
    (P : TheoremOne.ProblemFamily.{u}) : Prop where
  upper_certificates :
    TheoremOneEndToEnd.PairwiseCanonicalCaseBoundGeometricUpperCertificates P
  lower_realizations : TheoremOne.LowerRealizations P

/-- Strongest current geometric upper model.  Upper certificates provide
global circle coordinates, global normalized directions, and one canonical
crossing table; Lean derives the unordered four-direction close-pair theorem
by sorting each four-set. -/
structure CanonicalCoordinateGeometricModelSubtheorems
    (P : TheoremOne.ProblemFamily.{u}) : Prop where
  upper_certificates :
    TheoremOneEndToEnd.PairwiseCanonicalCoordinateGeometricUpperCertificates P
  lower_realizations : TheoremOne.LowerRealizations P

/-- Strongest current upper/lower model.  The upper side uses global circle
coordinates, normalized directions, and one canonical crossing table.  The
lower side supplies Karlsson blow-up crossing counts plus the generic
`regions = crossings + n + 1` equation; Lean derives the older lower
realization interface. -/
structure CanonicalCoordinateGeometricCrossingModelSubtheorems
    (P : TheoremOne.ProblemFamily.{u}) : Prop where
  upper_certificates :
    TheoremOneEndToEnd.PairwiseCanonicalCoordinateGeometricUpperCertificates P
  lower_crossing_realizations :
    ∃ lower_crossings : (n : Nat) → P.Arrangement n → Rat,
      TheoremOne.LowerCrossingRealizations P lower_crossings

/-- Strongest current exact-pairwise upper/lower model.  The upper side
supplies exact pairwise crossing counts and the exact region equation in
pair-sum form; Lean fills the older total-crossing fields.  The lower side
uses Karlsson blow-up crossing-count realizations plus the generic region
equation. -/
structure CanonicalExactCoordinateGeometricCrossingModelSubtheorems
    (P : TheoremOne.ProblemFamily.{u}) : Prop where
  upper_certificates :
    TheoremOneEndToEnd.PairwiseCanonicalExactCoordinateGeometricUpperCertificates P
  lower_crossing_realizations :
    ∃ lower_crossings : (n : Nat) → P.Arrangement n → Rat,
      TheoremOne.LowerCrossingRealizations P lower_crossings

/-- Convert the final model-specific package to the expanded end-to-end
subtheorem package. -/
def ModelSubtheorems.toEndToEndSubtheorems
    {P : TheoremOne.ProblemFamily.{u}}
    (h : ModelSubtheorems P) :
    TheoremOneEndToEnd.TheoremOneSubtheorems P where
  upper_certificates := h.upper_certificates
  lower_realizations := h.lower_realizations

/-- Convert the weighted-Turan model package to the previous final package by
choosing the weighted Turan partitions internally. -/
def WeightedTuranModelSubtheorems.toModelSubtheorems
    {P : TheoremOne.ProblemFamily.{u}}
    (h : WeightedTuranModelSubtheorems P) :
    ModelSubtheorems P where
  upper_certificates :=
    TheoremOneEndToEnd.pairwise_weighted_turan_upper_certificates_to_partition_matrix
      h.upper_certificates
  lower_realizations := h.lower_realizations

/-- Convert the colored-quotient model package to the weighted-Turan package by
deriving blocker graphs and clique-free complement hypotheses internally. -/
def ColoredQuotientModelSubtheorems.toWeightedTuranModelSubtheorems
    {P : TheoremOne.ProblemFamily.{u}}
    (h : ColoredQuotientModelSubtheorems P) :
    WeightedTuranModelSubtheorems P where
  upper_certificates :=
    TheoremOneEndToEnd.pairwise_colored_quotient_upper_certificates_to_weighted_turan
      h.upper_certificates
  lower_realizations := h.lower_realizations

/-- Convert the colored-quotient model package to the final model package. -/
def ColoredQuotientModelSubtheorems.toModelSubtheorems
    {P : TheoremOne.ProblemFamily.{u}}
    (h : ColoredQuotientModelSubtheorems P) :
    ModelSubtheorems P :=
  h.toWeightedTuranModelSubtheorems.toModelSubtheorems

/-- Convert the Paulsen-geometric package to the geometric package after Lean
derives the five-intriguing-pair fact from Paulsen's checked linear algebra. -/
noncomputable def PaulsenGeometricModelSubtheorems.toGeometricModelSubtheorems
    {P : TheoremOne.ProblemFamily.{u}}
    (h : PaulsenGeometricModelSubtheorems P) :
    GeometricModelSubtheorems P where
  upper_certificates :=
    TheoremOneEndToEnd.pairwise_paulsen_geometric_upper_certificates_to_geometric
      h.upper_certificates
  lower_realizations := h.lower_realizations

/-- Convert the Paulsen circle-coordinate package to the Paulsen vector package
after Lean performs the circle-vector Gram calculation. -/
noncomputable def PaulsenCircleGeometricModelSubtheorems.toPaulsenGeometricModelSubtheorems
    {P : TheoremOne.ProblemFamily.{u}}
    (h : PaulsenCircleGeometricModelSubtheorems P) :
    PaulsenGeometricModelSubtheorems P where
  upper_certificates :=
    TheoremOneEndToEnd.pairwise_paulsen_circle_geometric_upper_certificates_to_paulsen
      h.upper_certificates
  lower_realizations := h.lower_realizations

/-- Convert the Paulsen circle-coordinate package to the geometric package. -/
noncomputable def PaulsenCircleGeometricModelSubtheorems.toGeometricModelSubtheorems
    {P : TheoremOne.ProblemFamily.{u}}
    (h : PaulsenCircleGeometricModelSubtheorems P) :
    GeometricModelSubtheorems P :=
  h.toPaulsenGeometricModelSubtheorems.toGeometricModelSubtheorems

/-- Convert the global circle-coordinate package to the Paulsen circle package
after Lean restricts the global data to every five-subset. -/
noncomputable def GlobalCircleGeometricModelSubtheorems.toPaulsenCircleGeometricModelSubtheorems
    {P : TheoremOne.ProblemFamily.{u}}
    (h : GlobalCircleGeometricModelSubtheorems P) :
    PaulsenCircleGeometricModelSubtheorems P where
  upper_certificates :=
    TheoremOneEndToEnd.pairwise_global_circle_geometric_upper_certificates_to_paulsen_circle
      h.upper_certificates
  lower_realizations := h.lower_realizations

/-- Convert the global circle-coordinate package to the geometric package. -/
noncomputable def GlobalCircleGeometricModelSubtheorems.toGeometricModelSubtheorems
    {P : TheoremOne.ProblemFamily.{u}}
    (h : GlobalCircleGeometricModelSubtheorems P) :
    GeometricModelSubtheorems P :=
  h.toPaulsenCircleGeometricModelSubtheorems.toGeometricModelSubtheorems

/-- Convert the canonical circle-coordinate package to the global circle
package after Lean unfolds the canonical intriguing relation into distance
inequalities. -/
noncomputable def CanonicalCircleGeometricModelSubtheorems.toGlobalCircleGeometricModelSubtheorems
    {P : TheoremOne.ProblemFamily.{u}}
    (h : CanonicalCircleGeometricModelSubtheorems P) :
    GlobalCircleGeometricModelSubtheorems P where
  upper_certificates :=
    TheoremOneEndToEnd.pairwise_canonical_circle_geometric_upper_certificates_to_global
      h.upper_certificates
  lower_realizations := h.lower_realizations

/-- Convert the canonical circle-coordinate package to the geometric package. -/
noncomputable def CanonicalCircleGeometricModelSubtheorems.toGeometricModelSubtheorems
    {P : TheoremOne.ProblemFamily.{u}}
    (h : CanonicalCircleGeometricModelSubtheorems P) :
    GeometricModelSubtheorems P :=
  h.toGlobalCircleGeometricModelSubtheorems.toGeometricModelSubtheorems

/-- Convert the canonical geometric package to the canonical circle package
after Lean derives close-pair-in-four from the cyclic direction theorem. -/
noncomputable def CanonicalGeometricModelSubtheorems.toCanonicalCircleGeometricModelSubtheorems
    {P : TheoremOne.ProblemFamily.{u}}
    (h : CanonicalGeometricModelSubtheorems P) :
    CanonicalCircleGeometricModelSubtheorems P where
  upper_certificates :=
    TheoremOneEndToEnd.pairwise_canonical_geometric_upper_certificates_to_canonical_circle
      h.upper_certificates
  lower_realizations := h.lower_realizations

/-- Convert the canonical geometric package to the geometric package. -/
noncomputable def CanonicalGeometricModelSubtheorems.toGeometricModelSubtheorems
    {P : TheoremOne.ProblemFamily.{u}}
    (h : CanonicalGeometricModelSubtheorems P) :
    GeometricModelSubtheorems P :=
  h.toCanonicalCircleGeometricModelSubtheorems.toGeometricModelSubtheorems

/-- Convert the one-table canonical geometric package to the expanded
canonical geometric package by deriving the four pointwise crossing
inequality fields from the single case table. -/
noncomputable def CanonicalCaseBoundGeometricModelSubtheorems.toCanonicalGeometricModelSubtheorems
    {P : TheoremOne.ProblemFamily.{u}}
    (h : CanonicalCaseBoundGeometricModelSubtheorems P) :
    CanonicalGeometricModelSubtheorems P where
  upper_certificates :=
    TheoremOneEndToEnd.pairwise_canonical_case_bound_geometric_upper_certificates_to_canonical
      h.upper_certificates
  lower_realizations := h.lower_realizations

/-- Convert the one-table canonical geometric package to the geometric
package. -/
noncomputable def CanonicalCaseBoundGeometricModelSubtheorems.toGeometricModelSubtheorems
    {P : TheoremOne.ProblemFamily.{u}}
    (h : CanonicalCaseBoundGeometricModelSubtheorems P) :
    GeometricModelSubtheorems P :=
  h.toCanonicalGeometricModelSubtheorems.toGeometricModelSubtheorems

/-- Convert the coordinate package to the canonical-circle package by deriving
the close-pair-in-four theorem from unordered normalized directions and
expanding the crossing case table. -/
noncomputable def CanonicalCoordinateGeometricModelSubtheorems.toCanonicalCircleGeometricModelSubtheorems
    {P : TheoremOne.ProblemFamily.{u}}
    (h : CanonicalCoordinateGeometricModelSubtheorems P) :
    CanonicalCircleGeometricModelSubtheorems P where
  upper_certificates :=
    TheoremOneEndToEnd.pairwise_canonical_coordinate_geometric_upper_certificates_to_canonical_circle
      h.upper_certificates
  lower_realizations := h.lower_realizations

/-- Convert the coordinate package to the geometric package. -/
noncomputable def CanonicalCoordinateGeometricModelSubtheorems.toGeometricModelSubtheorems
    {P : TheoremOne.ProblemFamily.{u}}
    (h : CanonicalCoordinateGeometricModelSubtheorems P) :
    GeometricModelSubtheorems P :=
  h.toCanonicalCircleGeometricModelSubtheorems.toGeometricModelSubtheorems

/-- Convert the crossing-count lower package to the previous coordinate
package after deriving lower realizations from crossing counts and the generic
region equation. -/
noncomputable def CanonicalCoordinateGeometricCrossingModelSubtheorems.toCanonicalCoordinateGeometricModelSubtheorems
    {P : TheoremOne.ProblemFamily.{u}}
    (h : CanonicalCoordinateGeometricCrossingModelSubtheorems P) :
    CanonicalCoordinateGeometricModelSubtheorems P where
  upper_certificates := h.upper_certificates
  lower_realizations :=
    by
      rcases h.lower_crossing_realizations with ⟨lower_crossings, hlower⟩
      exact TheoremOne.lowerRealizations_of_lowerCrossingRealizations P
        (crossings := lower_crossings) hlower

/-- Convert exact-pairwise upper/lower data to the previous coordinate
crossing package by deriving the older coordinate upper certificates. -/
noncomputable def CanonicalExactCoordinateGeometricCrossingModelSubtheorems.toCanonicalCoordinateGeometricCrossingModelSubtheorems
    {P : TheoremOne.ProblemFamily.{u}}
    (h : CanonicalExactCoordinateGeometricCrossingModelSubtheorems P) :
    CanonicalCoordinateGeometricCrossingModelSubtheorems P where
  upper_certificates :=
    TheoremOneEndToEnd.pairwise_canonical_exact_coordinate_geometric_upper_certificates_to_coordinate
      h.upper_certificates
  lower_crossing_realizations := h.lower_crossing_realizations

/-- Convert exact-pairwise upper/lower data to the previous coordinate package. -/
noncomputable def CanonicalExactCoordinateGeometricCrossingModelSubtheorems.toCanonicalCoordinateGeometricModelSubtheorems
    {P : TheoremOne.ProblemFamily.{u}}
    (h : CanonicalExactCoordinateGeometricCrossingModelSubtheorems P) :
    CanonicalCoordinateGeometricModelSubtheorems P :=
  h.toCanonicalCoordinateGeometricCrossingModelSubtheorems
    |>.toCanonicalCoordinateGeometricModelSubtheorems

/-- Section 5's `3 x 4` matrix theorem is proved internally. -/
theorem section_five_matrix_theorem_proven : MatrixTheoremStatement :=
  matrix_theorem_proven

/-- The upper-bound half of Theorem 1 from the refined upper certificates.
All blocker, quotient, partition-intersection, pair-summation, and matrix
steps used here are proved in imported files. -/
theorem upper_bound_proven
    (P : TheoremOne.ProblemFamily.{u})
    (h : ModelSubtheorems P) :
    ∀ n : Nat, ∀ A : P.Arrangement n,
      P.region n A ≤ candidateRegionsChoose n := by
  exact TheoremOneEndToEnd.upper_bound_of_pairwise_partition_matrix_certificates
    P h.upper_certificates

/-- Upper-bound half of Theorem 1 from actual blocker graphs plus the proved
weighted Turan theorem. -/
theorem upper_bound_proven_from_weighted_turan
    (P : TheoremOne.ProblemFamily.{u})
    (h : WeightedTuranModelSubtheorems P) :
    ∀ n : Nat, ∀ A : P.Arrangement n,
      P.region n A ≤ candidateRegionsChoose n := by
  exact TheoremOneEndToEnd.upper_bound_of_pairwise_weighted_turan_certificates
    P h.upper_certificates

/-- Upper-bound half of Theorem 1 from no-zero colored quotient certificates.
All colored quotient, blocker, weighted Turan, partition-intersection,
pair-summation, and matrix steps used here are proved in imported files. -/
theorem upper_bound_proven_from_colored_quotients
    (P : TheoremOne.ProblemFamily.{u})
    (h : ColoredQuotientModelSubtheorems P) :
    ∀ n : Nat, ∀ A : P.Arrangement n,
      P.region n A ≤ candidateRegionsChoose n := by
  exact TheoremOneEndToEnd.upper_bound_of_pairwise_colored_quotient_certificates
    P h.upper_certificates

/-- Upper-bound half of Theorem 1 from original colored graph certificates.
This is the current strongest internalized upper path: colored Zykov and the
quotient construction are proved in Lean. -/
theorem upper_bound_proven_from_colored_graphs
    (P : TheoremOne.ProblemFamily.{u})
    (h : ColoredGraphModelSubtheorems P) :
    ∀ n : Nat, ∀ A : P.Arrangement n,
      P.region n A ≤ candidateRegionsChoose n := by
  exact TheoremOneEndToEnd.upper_bound_of_pairwise_colored_graph_certificates
    P h.upper_certificates

/-- Upper-bound half of Theorem 1 from the manuscript's close/intriguing
geometric upper data. -/
theorem upper_bound_proven_from_geometric_certificates
    (P : TheoremOne.ProblemFamily.{u})
    (h : GeometricModelSubtheorems P) :
    ∀ n : Nat, ∀ A : P.Arrangement n,
      P.region n A ≤ candidateRegionsChoose n := by
  exact TheoremOneEndToEnd.upper_bound_of_pairwise_geometric_certificates
    P h.upper_certificates

/-- Upper-bound half of Theorem 1 from geometric upper data where Paulsen
vector witnesses discharge the five-intriguing-pair input. -/
theorem upper_bound_proven_from_paulsen_geometric_certificates
    (P : TheoremOne.ProblemFamily.{u})
    (h : PaulsenGeometricModelSubtheorems P) :
    ∀ n : Nat, ∀ A : P.Arrangement n,
      P.region n A ≤ candidateRegionsChoose n := by
  exact TheoremOneEndToEnd.upper_bound_of_pairwise_paulsen_geometric_certificates
    P h.upper_certificates

/-- Upper-bound half of Theorem 1 from geometric upper data where Paulsen
circle-coordinate witnesses discharge the five-intriguing-pair input. -/
theorem upper_bound_proven_from_paulsen_circle_geometric_certificates
    (P : TheoremOne.ProblemFamily.{u})
    (h : PaulsenCircleGeometricModelSubtheorems P) :
    ∀ n : Nat, ∀ A : P.Arrangement n,
      P.region n A ≤ candidateRegionsChoose n := by
  exact TheoremOneEndToEnd.upper_bound_of_pairwise_paulsen_circle_geometric_certificates
    P h.upper_certificates

/-- Upper-bound half of Theorem 1 from one global circle-coordinate model per
arrangement. -/
theorem upper_bound_proven_from_global_circle_geometric_certificates
    (P : TheoremOne.ProblemFamily.{u})
    (h : GlobalCircleGeometricModelSubtheorems P) :
    ∀ n : Nat, ∀ A : P.Arrangement n,
      P.region n A ≤ candidateRegionsChoose n := by
  exact TheoremOneEndToEnd.upper_bound_of_pairwise_global_circle_geometric_certificates
    P h.upper_certificates

/-- Upper-bound half of Theorem 1 from one global circle-coordinate model per
arrangement, with `intriguing` fixed to the canonical Paulsen circle relation. -/
theorem upper_bound_proven_from_canonical_circle_geometric_certificates
    (P : TheoremOne.ProblemFamily.{u})
    (h : CanonicalCircleGeometricModelSubtheorems P) :
    ∀ n : Nat, ∀ A : P.Arrangement n,
      P.region n A ≤ candidateRegionsChoose n := by
  exact TheoremOneEndToEnd.upper_bound_of_pairwise_canonical_circle_geometric_certificates
    P h.upper_certificates

/-- Upper-bound half of Theorem 1 from canonical circle and direction
coordinate data. -/
theorem upper_bound_proven_from_canonical_geometric_certificates
    (P : TheoremOne.ProblemFamily.{u})
    (h : CanonicalGeometricModelSubtheorems P) :
    ∀ n : Nat, ∀ A : P.Arrangement n,
      P.region n A ≤ candidateRegionsChoose n := by
  exact TheoremOneEndToEnd.upper_bound_of_pairwise_canonical_geometric_certificates
    P h.upper_certificates

/-- Upper-bound half of Theorem 1 from canonical circle/direction coordinate
data and one canonical four-case crossing-count table. -/
theorem upper_bound_proven_from_canonical_case_bound_geometric_certificates
    (P : TheoremOne.ProblemFamily.{u})
    (h : CanonicalCaseBoundGeometricModelSubtheorems P) :
    ∀ n : Nat, ∀ A : P.Arrangement n,
      P.region n A ≤ candidateRegionsChoose n := by
  exact TheoremOneEndToEnd.upper_bound_of_pairwise_canonical_case_bound_geometric_certificates
    P h.upper_certificates

/-- Upper-bound half of Theorem 1 from global circle coordinates, global
normalized directions, and one canonical crossing table. -/
theorem upper_bound_proven_from_canonical_coordinate_geometric_certificates
    (P : TheoremOne.ProblemFamily.{u})
    (h : CanonicalCoordinateGeometricModelSubtheorems P) :
    ∀ n : Nat, ∀ A : P.Arrangement n,
      P.region n A ≤ candidateRegionsChoose n := by
  exact TheoremOneEndToEnd.upper_bound_of_pairwise_canonical_coordinate_geometric_certificates
    P h.upper_certificates

/-- Upper-bound half of Theorem 1 from the strongest current upper/lower
package.  The lower crossing data is unused for the upper half. -/
theorem upper_bound_proven_from_canonical_coordinate_geometric_crossing_certificates
    (P : TheoremOne.ProblemFamily.{u})
    (h : CanonicalCoordinateGeometricCrossingModelSubtheorems P) :
    ∀ n : Nat, ∀ A : P.Arrangement n,
      P.region n A ≤ candidateRegionsChoose n := by
  exact TheoremOneEndToEnd.upper_bound_of_pairwise_canonical_coordinate_geometric_certificates
    P h.upper_certificates

/-- Upper-bound half of Theorem 1 from exact pairwise crossing counts, global
circle coordinates, global normalized directions, and one canonical crossing
table.  The lower crossing data is unused for the upper half. -/
theorem upper_bound_proven_from_canonical_exact_coordinate_geometric_crossing_certificates
    (P : TheoremOne.ProblemFamily.{u})
    (h : CanonicalExactCoordinateGeometricCrossingModelSubtheorems P) :
    ∀ n : Nat, ∀ A : P.Arrangement n,
      P.region n A ≤ candidateRegionsChoose n := by
  exact TheoremOneEndToEnd.upper_bound_of_pairwise_canonical_exact_coordinate_geometric_certificates
    P h.upper_certificates

/-- The lower-attainment half of Theorem 1 from the lower-realization
certificates and the checked lower-construction algebra. -/
theorem lower_attainment_proven
    (P : TheoremOne.ProblemFamily.{u})
    (h : ModelSubtheorems P) :
    ∀ n : Nat, ∃ A : P.Arrangement n,
      P.region n A = candidateRegionsChoose n := by
  exact TheoremOneFormal.lower_attainment_of_realizations_choose
    P h.lower_realizations

/-- Theorem 1 in maximum form: the candidate value is attained and is an
upper bound for every arrangement. -/
theorem theorem_one_statement_proven
    (P : TheoremOne.ProblemFamily.{u})
    (h : ModelSubtheorems P) :
    TheoremOneStatement P := by
  exact TheoremOneEndToEnd.theorem_one_maximum
    P h.toEndToEndSubtheorems

/-- Theorem 1 in maximum form from the stronger weighted-Turan certificate
package. -/
theorem theorem_one_statement_proven_from_weighted_turan
    (P : TheoremOne.ProblemFamily.{u})
    (h : WeightedTuranModelSubtheorems P) :
    TheoremOneStatement P := by
  exact theorem_one_statement_proven P h.toModelSubtheorems

/-- Theorem 1 in maximum form from no-zero colored quotient upper certificates
and lower-realization certificates. -/
theorem theorem_one_statement_proven_from_colored_quotients
    (P : TheoremOne.ProblemFamily.{u})
    (h : ColoredQuotientModelSubtheorems P) :
    TheoremOneStatement P := by
  exact theorem_one_statement_proven P h.toModelSubtheorems

/-- Theorem 1 in maximum form from original colored graph upper certificates
and lower-realization certificates. -/
theorem theorem_one_statement_proven_from_colored_graphs
    (P : TheoremOne.ProblemFamily.{u})
    (h : ColoredGraphModelSubtheorems P) :
    TheoremOneStatement P := by
  exact TheoremOneFormal.maximumStatement_of_choose_upper_bound_and_lower_attainment
    P
    (upper_bound_proven_from_colored_graphs P h)
    (TheoremOneFormal.lower_attainment_of_realizations_choose
      P h.lower_realizations)

/-- Theorem 1 in maximum form from the manuscript's close/intriguing geometric
upper data and lower-realization certificates. -/
theorem theorem_one_statement_proven_from_geometric_certificates
    (P : TheoremOne.ProblemFamily.{u})
    (h : GeometricModelSubtheorems P) :
    TheoremOneStatement P := by
  exact TheoremOneFormal.maximumStatement_of_choose_upper_bound_and_lower_attainment
    P
    (upper_bound_proven_from_geometric_certificates P h)
    (TheoremOneFormal.lower_attainment_of_realizations_choose
      P h.lower_realizations)

/-- Theorem 1 in maximum form from Paulsen-geometric upper data and
lower-realization certificates. -/
theorem theorem_one_statement_proven_from_paulsen_geometric_certificates
    (P : TheoremOne.ProblemFamily.{u})
    (h : PaulsenGeometricModelSubtheorems P) :
    TheoremOneStatement P := by
  exact TheoremOneFormal.maximumStatement_of_choose_upper_bound_and_lower_attainment
    P
    (upper_bound_proven_from_paulsen_geometric_certificates P h)
    (TheoremOneFormal.lower_attainment_of_realizations_choose
      P h.lower_realizations)

/-- Theorem 1 in maximum form from Paulsen circle-coordinate geometric upper
data and lower-realization certificates. -/
theorem theorem_one_statement_proven_from_paulsen_circle_geometric_certificates
    (P : TheoremOne.ProblemFamily.{u})
    (h : PaulsenCircleGeometricModelSubtheorems P) :
    TheoremOneStatement P := by
  exact TheoremOneFormal.maximumStatement_of_choose_upper_bound_and_lower_attainment
    P
    (upper_bound_proven_from_paulsen_circle_geometric_certificates P h)
    (TheoremOneFormal.lower_attainment_of_realizations_choose
      P h.lower_realizations)

/-- Theorem 1 in maximum form from one global circle-coordinate upper model per
arrangement and lower-realization certificates. -/
theorem theorem_one_statement_proven_from_global_circle_geometric_certificates
    (P : TheoremOne.ProblemFamily.{u})
    (h : GlobalCircleGeometricModelSubtheorems P) :
    TheoremOneStatement P := by
  exact TheoremOneFormal.maximumStatement_of_choose_upper_bound_and_lower_attainment
    P
    (upper_bound_proven_from_global_circle_geometric_certificates P h)
    (TheoremOneFormal.lower_attainment_of_realizations_choose
      P h.lower_realizations)

/-- Theorem 1 in maximum form from canonical circle-coordinate upper data and
lower-realization certificates. -/
theorem theorem_one_statement_proven_from_canonical_circle_geometric_certificates
    (P : TheoremOne.ProblemFamily.{u})
    (h : CanonicalCircleGeometricModelSubtheorems P) :
    TheoremOneStatement P := by
  exact TheoremOneFormal.maximumStatement_of_choose_upper_bound_and_lower_attainment
    P
    (upper_bound_proven_from_canonical_circle_geometric_certificates P h)
    (TheoremOneFormal.lower_attainment_of_realizations_choose
      P h.lower_realizations)

/-- Theorem 1 in maximum form from canonical circle and direction upper data
and lower-realization certificates. -/
theorem theorem_one_statement_proven_from_canonical_geometric_certificates
    (P : TheoremOne.ProblemFamily.{u})
    (h : CanonicalGeometricModelSubtheorems P) :
    TheoremOneStatement P := by
  exact TheoremOneFormal.maximumStatement_of_choose_upper_bound_and_lower_attainment
    P
    (upper_bound_proven_from_canonical_geometric_certificates P h)
    (TheoremOneFormal.lower_attainment_of_realizations_choose
      P h.lower_realizations)

/-- Theorem 1 in maximum form from canonical circle/direction data, one
four-case crossing-count table, and lower-realization certificates. -/
theorem theorem_one_statement_proven_from_canonical_case_bound_geometric_certificates
    (P : TheoremOne.ProblemFamily.{u})
    (h : CanonicalCaseBoundGeometricModelSubtheorems P) :
    TheoremOneStatement P := by
  exact TheoremOneFormal.maximumStatement_of_choose_upper_bound_and_lower_attainment
    P
    (upper_bound_proven_from_canonical_case_bound_geometric_certificates P h)
    (TheoremOneFormal.lower_attainment_of_realizations_choose
      P h.lower_realizations)

/-- Theorem 1 in maximum form from global circle coordinates, global
normalized directions, one canonical crossing table, and lower-realization
certificates. -/
theorem theorem_one_statement_proven_from_canonical_coordinate_geometric_certificates
    (P : TheoremOne.ProblemFamily.{u})
    (h : CanonicalCoordinateGeometricModelSubtheorems P) :
    TheoremOneStatement P := by
  exact TheoremOneFormal.maximumStatement_of_choose_upper_bound_and_lower_attainment
    P
    (upper_bound_proven_from_canonical_coordinate_geometric_certificates P h)
    (TheoremOneFormal.lower_attainment_of_realizations_choose
      P h.lower_realizations)

/-- Theorem 1 in maximum form from global circle coordinates, global
normalized directions, one canonical crossing table, lower Karlsson
crossing-count realizations, and the generic region equation. -/
theorem theorem_one_statement_proven_from_canonical_coordinate_geometric_crossing_certificates
    (P : TheoremOne.ProblemFamily.{u})
    (h : CanonicalCoordinateGeometricCrossingModelSubtheorems P) :
    TheoremOneStatement P := by
  exact theorem_one_statement_proven_from_canonical_coordinate_geometric_certificates
    P h.toCanonicalCoordinateGeometricModelSubtheorems

/-- Theorem 1 in maximum form from exact pairwise upper data, global circle
coordinates, global normalized directions, one canonical crossing table,
lower Karlsson crossing-count realizations, and the generic region equation. -/
theorem theorem_one_statement_proven_from_canonical_exact_coordinate_geometric_crossing_certificates
    (P : TheoremOne.ProblemFamily.{u})
    (h : CanonicalExactCoordinateGeometricCrossingModelSubtheorems P) :
    TheoremOneStatement P := by
  exact theorem_one_statement_proven_from_canonical_coordinate_geometric_crossing_certificates
    P h.toCanonicalCoordinateGeometricCrossingModelSubtheorems

/-- Final inputs for a family with a named maximum-count function. -/
def MaxModelSubtheorems (P : TheoremOne.MaxProblemFamily.{u}) : Prop :=
  ModelSubtheorems P.toProblemFamily

/-- Final weighted-Turan inputs for a family with a named maximum-count
function. -/
def MaxWeightedTuranModelSubtheorems
    (P : TheoremOne.MaxProblemFamily.{u}) : Prop :=
  WeightedTuranModelSubtheorems P.toProblemFamily

/-- Final colored-quotient inputs for a family with a named maximum-count
function. -/
def MaxColoredQuotientModelSubtheorems
    (P : TheoremOne.MaxProblemFamily.{u}) : Prop :=
  ColoredQuotientModelSubtheorems P.toProblemFamily

/-- Final colored-graph inputs for a family with a named maximum-count
function. -/
def MaxColoredGraphModelSubtheorems
    (P : TheoremOne.MaxProblemFamily.{u}) : Prop :=
  ColoredGraphModelSubtheorems P.toProblemFamily

/-- Final geometric inputs for a family with a named maximum-count function. -/
def MaxGeometricModelSubtheorems
    (P : TheoremOne.MaxProblemFamily.{u}) : Prop :=
  GeometricModelSubtheorems P.toProblemFamily

/-- Final Paulsen-geometric inputs for a family with a named maximum-count
function. -/
def MaxPaulsenGeometricModelSubtheorems
    (P : TheoremOne.MaxProblemFamily.{u}) : Prop :=
  PaulsenGeometricModelSubtheorems P.toProblemFamily

/-- Final Paulsen circle-coordinate geometric inputs for a family with a named
maximum-count function. -/
def MaxPaulsenCircleGeometricModelSubtheorems
    (P : TheoremOne.MaxProblemFamily.{u}) : Prop :=
  PaulsenCircleGeometricModelSubtheorems P.toProblemFamily

/-- Final global circle-coordinate geometric inputs for a family with a named
maximum-count function. -/
def MaxGlobalCircleGeometricModelSubtheorems
    (P : TheoremOne.MaxProblemFamily.{u}) : Prop :=
  GlobalCircleGeometricModelSubtheorems P.toProblemFamily

/-- Final canonical circle-coordinate geometric inputs for a family with a
named maximum-count function. -/
def MaxCanonicalCircleGeometricModelSubtheorems
    (P : TheoremOne.MaxProblemFamily.{u}) : Prop :=
  CanonicalCircleGeometricModelSubtheorems P.toProblemFamily

/-- Final canonical circle and direction geometric inputs for a family with a
named maximum-count function. -/
def MaxCanonicalGeometricModelSubtheorems
    (P : TheoremOne.MaxProblemFamily.{u}) : Prop :=
  CanonicalGeometricModelSubtheorems P.toProblemFamily

/-- Final one-table canonical geometric inputs for a family with a named
maximum-count function. -/
def MaxCanonicalCaseBoundGeometricModelSubtheorems
    (P : TheoremOne.MaxProblemFamily.{u}) : Prop :=
  CanonicalCaseBoundGeometricModelSubtheorems P.toProblemFamily

/-- Final coordinate geometric inputs for a family with a named maximum-count
function. -/
def MaxCanonicalCoordinateGeometricModelSubtheorems
    (P : TheoremOne.MaxProblemFamily.{u}) : Prop :=
  CanonicalCoordinateGeometricModelSubtheorems P.toProblemFamily

/-- Final coordinate upper and lower-crossing inputs for a family with a named
maximum-count function. -/
def MaxCanonicalCoordinateGeometricCrossingModelSubtheorems
    (P : TheoremOne.MaxProblemFamily.{u}) : Prop :=
  CanonicalCoordinateGeometricCrossingModelSubtheorems P.toProblemFamily

/-- Final exact-pairwise coordinate upper and lower-crossing inputs for a
family with a named maximum-count function. -/
def MaxCanonicalExactCoordinateGeometricCrossingModelSubtheorems
    (P : TheoremOne.MaxProblemFamily.{u}) : Prop :=
  CanonicalExactCoordinateGeometricCrossingModelSubtheorems P.toProblemFamily

/-- Theorem 1 in formula form for a named maximum-count function. -/
theorem theorem_one_formula_statement_proven
    (P : TheoremOne.MaxProblemFamily.{u})
    (h : MaxModelSubtheorems P) :
    TheoremOneFormulaStatement P := by
  exact TheoremOneEndToEnd.theorem_one_formula P
    h.toEndToEndSubtheorems

/-- Theorem 1 in formula form from the stronger weighted-Turan certificate
package. -/
theorem theorem_one_formula_statement_proven_from_weighted_turan
    (P : TheoremOne.MaxProblemFamily.{u})
    (h : MaxWeightedTuranModelSubtheorems P) :
    TheoremOneFormulaStatement P := by
  exact theorem_one_formula_statement_proven P h.toModelSubtheorems

/-- Theorem 1 in formula form from no-zero colored quotient upper certificates
and lower-realization certificates. -/
theorem theorem_one_formula_statement_proven_from_colored_quotients
    (P : TheoremOne.MaxProblemFamily.{u})
    (h : MaxColoredQuotientModelSubtheorems P) :
    TheoremOneFormulaStatement P := by
  exact theorem_one_formula_statement_proven P h.toModelSubtheorems

/-- Theorem 1 in formula form from original colored graph upper certificates
and lower-realization certificates. -/
theorem theorem_one_formula_statement_proven_from_colored_graphs
    (P : TheoremOne.MaxProblemFamily.{u})
    (h : MaxColoredGraphModelSubtheorems P) :
    TheoremOneFormulaStatement P := by
  exact TheoremOne.formulaStatement_of_maximumStatement P
    (theorem_one_statement_proven_from_colored_graphs P.toProblemFamily h)

/-- Theorem 1 in formula form from the manuscript's close/intriguing geometric
upper data and lower-realization certificates. -/
theorem theorem_one_formula_statement_proven_from_geometric_certificates
    (P : TheoremOne.MaxProblemFamily.{u})
    (h : MaxGeometricModelSubtheorems P) :
    TheoremOneFormulaStatement P := by
  exact TheoremOne.formulaStatement_of_maximumStatement P
    (theorem_one_statement_proven_from_geometric_certificates
      P.toProblemFamily h)

/-- Theorem 1 in formula form from Paulsen-geometric upper data and
lower-realization certificates. -/
theorem theorem_one_formula_statement_proven_from_paulsen_geometric_certificates
    (P : TheoremOne.MaxProblemFamily.{u})
    (h : MaxPaulsenGeometricModelSubtheorems P) :
    TheoremOneFormulaStatement P := by
  exact TheoremOne.formulaStatement_of_maximumStatement P
    (theorem_one_statement_proven_from_paulsen_geometric_certificates
      P.toProblemFamily h)

/-- Theorem 1 in formula form from Paulsen circle-coordinate geometric upper
data and lower-realization certificates. -/
theorem theorem_one_formula_statement_proven_from_paulsen_circle_geometric_certificates
    (P : TheoremOne.MaxProblemFamily.{u})
    (h : MaxPaulsenCircleGeometricModelSubtheorems P) :
    TheoremOneFormulaStatement P := by
  exact TheoremOne.formulaStatement_of_maximumStatement P
    (theorem_one_statement_proven_from_paulsen_circle_geometric_certificates
      P.toProblemFamily h)

/-- Theorem 1 in formula form from one global circle-coordinate upper model
per arrangement and lower-realization certificates. -/
theorem theorem_one_formula_statement_proven_from_global_circle_geometric_certificates
    (P : TheoremOne.MaxProblemFamily.{u})
    (h : MaxGlobalCircleGeometricModelSubtheorems P) :
    TheoremOneFormulaStatement P := by
  exact TheoremOne.formulaStatement_of_maximumStatement P
    (theorem_one_statement_proven_from_global_circle_geometric_certificates
      P.toProblemFamily h)

/-- Theorem 1 in formula form from canonical circle-coordinate upper data and
lower-realization certificates. -/
theorem theorem_one_formula_statement_proven_from_canonical_circle_geometric_certificates
    (P : TheoremOne.MaxProblemFamily.{u})
    (h : MaxCanonicalCircleGeometricModelSubtheorems P) :
    TheoremOneFormulaStatement P := by
  exact TheoremOne.formulaStatement_of_maximumStatement P
    (theorem_one_statement_proven_from_canonical_circle_geometric_certificates
      P.toProblemFamily h)

/-- Theorem 1 in formula form from canonical circle and direction upper data
and lower-realization certificates. -/
theorem theorem_one_formula_statement_proven_from_canonical_geometric_certificates
    (P : TheoremOne.MaxProblemFamily.{u})
    (h : MaxCanonicalGeometricModelSubtheorems P) :
    TheoremOneFormulaStatement P := by
  exact TheoremOne.formulaStatement_of_maximumStatement P
    (theorem_one_statement_proven_from_canonical_geometric_certificates
      P.toProblemFamily h)

/-- Theorem 1 in formula form from canonical circle/direction data, one
four-case crossing-count table, and lower-realization certificates. -/
theorem theorem_one_formula_statement_proven_from_canonical_case_bound_geometric_certificates
    (P : TheoremOne.MaxProblemFamily.{u})
    (h : MaxCanonicalCaseBoundGeometricModelSubtheorems P) :
    TheoremOneFormulaStatement P := by
  exact TheoremOne.formulaStatement_of_maximumStatement P
    (theorem_one_statement_proven_from_canonical_case_bound_geometric_certificates
      P.toProblemFamily h)

/-- Theorem 1 in formula form from global circle coordinates, global
normalized directions, one canonical crossing table, and lower-realization
certificates. -/
theorem theorem_one_formula_statement_proven_from_canonical_coordinate_geometric_certificates
    (P : TheoremOne.MaxProblemFamily.{u})
    (h : MaxCanonicalCoordinateGeometricModelSubtheorems P) :
    TheoremOneFormulaStatement P := by
  exact TheoremOne.formulaStatement_of_maximumStatement P
    (theorem_one_statement_proven_from_canonical_coordinate_geometric_certificates
      P.toProblemFamily h)

/-- Theorem 1 in formula form from the strongest current upper/lower package,
using lower crossing counts plus `regions = crossings + n + 1`. -/
theorem theorem_one_formula_statement_proven_from_canonical_coordinate_geometric_crossing_certificates
    (P : TheoremOne.MaxProblemFamily.{u})
    (h : MaxCanonicalCoordinateGeometricCrossingModelSubtheorems P) :
    TheoremOneFormulaStatement P := by
  exact TheoremOne.formulaStatement_of_maximumStatement P
    (theorem_one_statement_proven_from_canonical_coordinate_geometric_crossing_certificates
      P.toProblemFamily h)

/-- Theorem 1 in formula form from the strongest exact-pairwise upper/lower
package. -/
theorem theorem_one_formula_statement_proven_from_canonical_exact_coordinate_geometric_crossing_certificates
    (P : TheoremOne.MaxProblemFamily.{u})
    (h : MaxCanonicalExactCoordinateGeometricCrossingModelSubtheorems P) :
    TheoremOneFormulaStatement P := by
  exact TheoremOne.formulaStatement_of_maximumStatement P
    (theorem_one_statement_proven_from_canonical_exact_coordinate_geometric_crossing_certificates
      P.toProblemFamily h)

/-- Single-size displayed formula. -/
theorem theorem_one_formula_at_proven
    (P : TheoremOne.MaxProblemFamily.{u})
    (h : MaxModelSubtheorems P)
    (n : Nat) :
    P.aLop n =
      4 * ((n.choose 2 : Nat) : Rat) + concreteS n + (n : Rat) + 1 := by
  exact theorem_one_formula_statement_proven P h n

/-- Single-size displayed formula from the stronger weighted-Turan certificate
package. -/
theorem theorem_one_formula_at_proven_from_weighted_turan
    (P : TheoremOne.MaxProblemFamily.{u})
    (h : MaxWeightedTuranModelSubtheorems P)
    (n : Nat) :
    P.aLop n =
      4 * ((n.choose 2 : Nat) : Rat) + concreteS n + (n : Rat) + 1 := by
  exact theorem_one_formula_statement_proven_from_weighted_turan P h n

/-- Single-size displayed formula from no-zero colored quotient upper
certificates and lower-realization certificates. -/
theorem theorem_one_formula_at_proven_from_colored_quotients
    (P : TheoremOne.MaxProblemFamily.{u})
    (h : MaxColoredQuotientModelSubtheorems P)
    (n : Nat) :
    P.aLop n =
      4 * ((n.choose 2 : Nat) : Rat) + concreteS n + (n : Rat) + 1 := by
  exact theorem_one_formula_statement_proven_from_colored_quotients P h n

/-- Single-size displayed formula from original colored graph upper
certificates and lower-realization certificates. -/
theorem theorem_one_formula_at_proven_from_colored_graphs
    (P : TheoremOne.MaxProblemFamily.{u})
    (h : MaxColoredGraphModelSubtheorems P)
    (n : Nat) :
    P.aLop n =
      4 * ((n.choose 2 : Nat) : Rat) + concreteS n + (n : Rat) + 1 := by
  exact theorem_one_formula_statement_proven_from_colored_graphs P h n

/-- Single-size displayed formula from the manuscript's close/intriguing
geometric upper data and lower-realization certificates. -/
theorem theorem_one_formula_at_proven_from_geometric_certificates
    (P : TheoremOne.MaxProblemFamily.{u})
    (h : MaxGeometricModelSubtheorems P)
    (n : Nat) :
    P.aLop n =
      4 * ((n.choose 2 : Nat) : Rat) + concreteS n + (n : Rat) + 1 := by
  exact theorem_one_formula_statement_proven_from_geometric_certificates P h n

/-- Single-size displayed formula from Paulsen-geometric upper data and
lower-realization certificates. -/
theorem theorem_one_formula_at_proven_from_paulsen_geometric_certificates
    (P : TheoremOne.MaxProblemFamily.{u})
    (h : MaxPaulsenGeometricModelSubtheorems P)
    (n : Nat) :
    P.aLop n =
      4 * ((n.choose 2 : Nat) : Rat) + concreteS n + (n : Rat) + 1 := by
  exact theorem_one_formula_statement_proven_from_paulsen_geometric_certificates P h n

/-- Single-size displayed formula from Paulsen circle-coordinate geometric
upper data and lower-realization certificates. -/
theorem theorem_one_formula_at_proven_from_paulsen_circle_geometric_certificates
    (P : TheoremOne.MaxProblemFamily.{u})
    (h : MaxPaulsenCircleGeometricModelSubtheorems P)
    (n : Nat) :
    P.aLop n =
      4 * ((n.choose 2 : Nat) : Rat) + concreteS n + (n : Rat) + 1 := by
  exact theorem_one_formula_statement_proven_from_paulsen_circle_geometric_certificates P h n

/-- Single-size displayed formula from one global circle-coordinate upper model
per arrangement and lower-realization certificates. -/
theorem theorem_one_formula_at_proven_from_global_circle_geometric_certificates
    (P : TheoremOne.MaxProblemFamily.{u})
    (h : MaxGlobalCircleGeometricModelSubtheorems P)
    (n : Nat) :
    P.aLop n =
      4 * ((n.choose 2 : Nat) : Rat) + concreteS n + (n : Rat) + 1 := by
  exact theorem_one_formula_statement_proven_from_global_circle_geometric_certificates P h n

/-- Single-size displayed formula from canonical circle-coordinate upper data
and lower-realization certificates. -/
theorem theorem_one_formula_at_proven_from_canonical_circle_geometric_certificates
    (P : TheoremOne.MaxProblemFamily.{u})
    (h : MaxCanonicalCircleGeometricModelSubtheorems P)
    (n : Nat) :
    P.aLop n =
      4 * ((n.choose 2 : Nat) : Rat) + concreteS n + (n : Rat) + 1 := by
  exact theorem_one_formula_statement_proven_from_canonical_circle_geometric_certificates P h n

/-- Single-size displayed formula from canonical circle and direction upper
data and lower-realization certificates. -/
theorem theorem_one_formula_at_proven_from_canonical_geometric_certificates
    (P : TheoremOne.MaxProblemFamily.{u})
    (h : MaxCanonicalGeometricModelSubtheorems P)
    (n : Nat) :
    P.aLop n =
      4 * ((n.choose 2 : Nat) : Rat) + concreteS n + (n : Rat) + 1 := by
  exact theorem_one_formula_statement_proven_from_canonical_geometric_certificates P h n

/-- Single-size displayed formula from canonical circle/direction data, one
four-case crossing-count table, and lower-realization certificates. -/
theorem theorem_one_formula_at_proven_from_canonical_case_bound_geometric_certificates
    (P : TheoremOne.MaxProblemFamily.{u})
    (h : MaxCanonicalCaseBoundGeometricModelSubtheorems P)
    (n : Nat) :
    P.aLop n =
      4 * ((n.choose 2 : Nat) : Rat) + concreteS n + (n : Rat) + 1 := by
  exact theorem_one_formula_statement_proven_from_canonical_case_bound_geometric_certificates P h n

/-- Single-size displayed formula from global circle coordinates, global
normalized directions, one canonical crossing table, and lower-realization
certificates. -/
theorem theorem_one_formula_at_proven_from_canonical_coordinate_geometric_certificates
    (P : TheoremOne.MaxProblemFamily.{u})
    (h : MaxCanonicalCoordinateGeometricModelSubtheorems P)
    (n : Nat) :
    P.aLop n =
      4 * ((n.choose 2 : Nat) : Rat) + concreteS n + (n : Rat) + 1 := by
  exact theorem_one_formula_statement_proven_from_canonical_coordinate_geometric_certificates P h n

/-- Single-size displayed formula from the strongest current upper/lower
package, using lower crossing counts plus `regions = crossings + n + 1`. -/
theorem theorem_one_formula_at_proven_from_canonical_coordinate_geometric_crossing_certificates
    (P : TheoremOne.MaxProblemFamily.{u})
    (h : MaxCanonicalCoordinateGeometricCrossingModelSubtheorems P)
    (n : Nat) :
    P.aLop n =
      4 * ((n.choose 2 : Nat) : Rat) + concreteS n + (n : Rat) + 1 := by
  exact theorem_one_formula_statement_proven_from_canonical_coordinate_geometric_crossing_certificates P h n

/-- Single-size displayed formula from the strongest exact-pairwise upper/lower
package. -/
theorem theorem_one_formula_at_proven_from_canonical_exact_coordinate_geometric_crossing_certificates
    (P : TheoremOne.MaxProblemFamily.{u})
    (h : MaxCanonicalExactCoordinateGeometricCrossingModelSubtheorems P)
    (n : Nat) :
    P.aLop n =
      4 * ((n.choose 2 : Nat) : Rat) + concreteS n + (n : Rat) + 1 := by
  exact theorem_one_formula_statement_proven_from_canonical_exact_coordinate_geometric_crossing_certificates P h n

end TheoremOneFinal
end Lollipop
