import Lollipop.Internal.Manuscript.FormalizedProof.DependencyGraph

/-!
First-principles boundary for manuscript Theorem 1.

This module is deliberately separate from the existing formalized proof stack.
It records the exact certificate boundary that would close Theorem 1 from
Euclidean lollipop geometry and Karlsson's lower construction.  The theorem at
the bottom is fully proved from these certificates through the radial
manuscript catalogue endpoint; the certificate fields are the remaining
model-specific construction obligations.
-/

namespace Lollipop
namespace TheoremOneManuscript
namespace FirstPrinciples

universe u

/-- The upper Euclidean certificate currently needed for a first-principles
Theorem 1 proof: primitive lollipop carriers, radial-outward stems, finite
carrier-intersection crossing witnesses, generic noncoincidence, and
component-wise close/intriguing savings. -/
abbrev EuclideanUpperCertificate
    (P : TheoremOne.ProblemFamily.{u}) : Type u :=
  PrimitiveGeometry.PrimitiveRadialCarrierComponentSavingsUpperGeometryData P

/-- The lower certificate currently needed for a first-principles Theorem 1
proof: Karlsson's four-base table, a four-base region-increment certificate,
and sorted local blow-up arrangements with pairwise crossing and insertion
data. -/
abbrev KarlssonLowerCertificate
    (P : TheoremOne.ProblemFamily.{u}) : Type u :=
  ExplicitInputs.KarlssonBaseBlowUpIncrementalLowerData P

/-- The complete current first-principles boundary for manuscript Theorem 1.

Supplying a term of this structure means all generic combinatorial, algebraic,
and finite-counting lemmas are already available in Lean; only the two concrete
model constructors below have to be built. -/
structure TheoremOneCertificates
    (P : TheoremOne.MaxProblemFamily.{u}) : Type u where
  upper : EuclideanUpperCertificate P.toProblemFamily
  lower : KarlssonLowerCertificate P.toProblemFamily

namespace EuclideanUpperCertificate

/-- Upper certificates supply actual primitive arrangements. -/
def provided_arrangements
    {P : TheoremOne.ProblemFamily.{u}}
    (h : EuclideanUpperCertificate P) :
    ∀ n : Nat, P.Arrangement n → PrimitiveGeometry.EuclideanLollipopArrangement n :=
  h.arrangement

/-- Upper certificates supply a pairwise crossing table. -/
def provided_pair_crossing_table
    {P : TheoremOne.ProblemFamily.{u}}
    (h : EuclideanUpperCertificate P) :
    ∀ n : Nat, P.Arrangement n → Fin n → Fin n → Rat :=
  h.cross

/-- Upper certificates identify each pair table entry with a finite carrier
intersection witness. -/
def provided_finite_carrier_intersections
    {P : TheoremOne.ProblemFamily.{u}}
    (h : EuclideanUpperCertificate P) :
    ∀ n : Nat, ∀ A : P.Arrangement n,
      PrimitiveGeometry.PairwiseCarrierCrossingData
        (h.arrangement n A) (h.cross n A) :=
  h.pairwise_crossings

/-- Upper certificates prove distinct circle carriers for every unordered pair. -/
theorem provided_spheres_distinct
    {P : TheoremOne.ProblemFamily.{u}}
    (h : EuclideanUpperCertificate P) :
    ∀ n : Nat, ∀ A : P.Arrangement n, ∀ i j : Fin n, i < j →
      PrimitiveGeometry.euclideanSphere ((h.arrangement n A).lollipop i).center
          ((h.arrangement n A).lollipop i).radius ≠
        PrimitiveGeometry.euclideanSphere ((h.arrangement n A).lollipop j).center
          ((h.arrangement n A).lollipop j).radius :=
  h.spheres_distinct

/-- Upper certificates prove distinct ray-supporting lines for every unordered
pair. -/
theorem provided_ray_lines_distinct
    {P : TheoremOne.ProblemFamily.{u}}
    (h : EuclideanUpperCertificate P) :
    ∀ n : Nat, ∀ A : P.Arrangement n, ∀ i j : Fin n, i < j →
      PrimitiveGeometry.euclideanRayLine ((h.arrangement n A).lollipop i) ≠
        PrimitiveGeometry.euclideanRayLine ((h.arrangement n A).lollipop j) :=
  h.rayLines_distinct

/-- Upper certificates give component-wise savings for close pairs. -/
def provided_close_savings
    {P : TheoremOne.ProblemFamily.{u}}
    (h : EuclideanUpperCertificate P) :
    ∀ n : Nat, ∀ A : P.Arrangement n, ∀ i j : Fin n, i < j →
      TheoremOneEndToEnd.CloseDirection.cyclicClose
        (fun k => (h.arrangement n A).normalizedDirection k) i j →
        PrimitiveGeometry.PairComponentSavings ((h.arrangement n A).lollipop i)
          ((h.arrangement n A).lollipop j) 5 :=
  h.close_savings

/-- Upper certificates give component-wise savings for intriguing pairs. -/
def provided_intriguing_savings
    {P : TheoremOne.ProblemFamily.{u}}
    (h : EuclideanUpperCertificate P) :
    ∀ n : Nat, ∀ A : P.Arrangement n, ∀ i j : Fin n, i < j →
      TheoremOneEndToEnd.PaulsenLinearAlgebra.circleIntriguing
        (fun k => (h.arrangement n A).center k)
        (fun k => (h.arrangement n A).radius k) i j →
        PrimitiveGeometry.PairComponentSavings ((h.arrangement n A).lollipop i)
          ((h.arrangement n A).lollipop j) 5 :=
  h.intriguing_savings

/-- Upper certificates give the stronger component-wise savings for pairs that
are both close and intriguing. -/
def provided_close_intriguing_savings
    {P : TheoremOne.ProblemFamily.{u}}
    (h : EuclideanUpperCertificate P) :
    ∀ n : Nat, ∀ A : P.Arrangement n, ∀ i j : Fin n, i < j →
      TheoremOneEndToEnd.CloseDirection.cyclicClose
        (fun k => (h.arrangement n A).normalizedDirection k) i j →
      TheoremOneEndToEnd.PaulsenLinearAlgebra.circleIntriguing
        (fun k => (h.arrangement n A).center k)
        (fun k => (h.arrangement n A).radius k) i j →
        PrimitiveGeometry.PairComponentSavings ((h.arrangement n A).lollipop i)
          ((h.arrangement n A).lollipop j) 4 :=
  h.close_intriguing_savings

/-- Upper certificates supply the ordered insertion-region equation for their
pairwise crossing table. -/
def provided_region_increment
    {P : TheoremOne.ProblemFamily.{u}}
    (h : EuclideanUpperCertificate P) :
    ∀ n : Nat, ∀ A : P.Arrangement n,
      OrderedIncrementalPairRegionData n (P.region n A) (h.cross n A) :=
  h.region_increment

/-- Upper certificates record that every stem is radial outward, matching the
manuscript lollipop convention. -/
theorem provided_radial_outward
    {P : TheoremOne.ProblemFamily.{u}}
    (h : EuclideanUpperCertificate P) :
    ∀ n : Nat, ∀ A : P.Arrangement n, ∀ i : Fin n,
      ((h.arrangement n A).lollipop i).IsRadialOutward :=
  h.radial_outward

end EuclideanUpperCertificate

namespace KarlssonLowerCertificate

/-- Lower certificates contain the four-lollipop Karlsson base arrangement. -/
def provided_base_arrangement
    {P : TheoremOne.ProblemFamily.{u}}
    (h : KarlssonLowerCertificate P) :
    P.Arrangement 4 :=
  h.base_arrangement

/-- Lower certificates contain a four-base pair table. -/
def provided_base_pair_table
    {P : TheoremOne.ProblemFamily.{u}}
    (h : KarlssonLowerCertificate P) :
    Fin 4 → Fin 4 → Rat :=
  h.base_pair_cross

/-- Lower certificates prove the four-base pair table is Karlsson's displayed
`5,7,7,7,7,7` table on distinct base pairs. -/
theorem provided_base_pair_table_eq_karlsson
    {P : TheoremOne.ProblemFamily.{u}}
    (h : KarlssonLowerCertificate P) :
    ∀ a b : Fin 4, a ≠ b →
      h.base_pair_cross a b = ExplicitInputs.karlssonBasePairCrossing a b :=
  h.base_pair_cross_eq_karlsson

/-- Lower certificates prove the ordered insertion-region equation for the
four-base arrangement. -/
def provided_base_region_increment
    {P : TheoremOne.ProblemFamily.{u}}
    (h : KarlssonLowerCertificate P) :
    OrderedIncrementalPairRegionData 4
      (P.region 4 h.base_arrangement) h.base_pair_cross :=
  h.base_region_increment

/-- Lower certificates produce one blow-up arrangement for each sorted quadruple
of cluster sizes. -/
def provided_blowup_arrangements
    {P : TheoremOne.ProblemFamily.{u}}
    (h : KarlssonLowerCertificate P) :
    ∀ n : Nat, (q : QuadVec n) → q ∈ sortedQuadVecs n →
      P.Arrangement n :=
  h.arrangement

/-- Lower certificates provide the canonical cardinality-cluster witness for
each sorted quadruple. -/
def provided_cluster_witnesses
    {P : TheoremOne.ProblemFamily.{u}}
    (h : KarlssonLowerCertificate P) :
    ∀ n : Nat, (q : QuadVec n) → q ∈ sortedQuadVecs n →
      ExplicitInputs.CardinalityClusteredKarlssonTableWitness q :=
  h.cluster_witness

/-- Lower certificates provide a pairwise crossing table for produced
arrangements. -/
def provided_pair_crossing_table
    {P : TheoremOne.ProblemFamily.{u}}
    (h : KarlssonLowerCertificate P) :
    ∀ n : Nat, P.Arrangement n → Fin n → Fin n → Rat :=
  h.pair_cross

/-- Lower certificates prove each copy-pair value is inherited from either the
same-cluster value or the appropriate Karlsson base pair value. -/
theorem provided_pair_crossing_eq_base_copy
    {P : TheoremOne.ProblemFamily.{u}}
    (h : KarlssonLowerCertificate P) :
    ∀ (n : Nat) (q : QuadVec n) (hq : q ∈ sortedQuadVecs n),
      ∀ i j : Fin n, i < j →
        h.pair_cross n (h.arrangement n q hq) i j =
          ExplicitInputs.karlssonBaseCopyPairCrossing h.base_pair_cross
            ((h.cluster_witness n q hq).cluster) i j :=
  h.pair_cross_eq_base_copy

/-- Lower certificates supply ordered insertion-region equations for every
produced blow-up arrangement. -/
def provided_region_increment
    {P : TheoremOne.ProblemFamily.{u}}
    (h : KarlssonLowerCertificate P) :
    ∀ (n : Nat) (q : QuadVec n) (hq : q ∈ sortedQuadVecs n),
      OrderedIncrementalPairRegionData n
        (P.region n (h.arrangement n q hq))
        (h.pair_cross n (h.arrangement n q hq)) :=
  h.region_increment

end KarlssonLowerCertificate

namespace TheoremOneCertificates

/-- Convert the explicit first-principles boundary into the radial proof-DAG
used by the manuscript catalogue. -/
noncomputable def toRadialDependencyGraph
    {P : TheoremOne.MaxProblemFamily.{u}}
    (h : TheoremOneCertificates P) :
    FormalizedProof.RadialTheoremOneDependencyGraph P where
  upper_geometry := h.upper
  lower_karlsson_base := h.lower

end TheoremOneCertificates

/-- Manuscript Theorem 1 follows from the current first-principles boundary. -/
theorem theorem_one_from_first_principles_boundary
    (P : TheoremOne.MaxProblemFamily.{u})
    (h : TheoremOneCertificates P) :
    FormalizedProof.FinalTheoremOneStatement P :=
  FormalizedProof.theorem_one_from_radial_dependency_graph P
    h.toRadialDependencyGraph

/-- Single-size form of Theorem 1 from the current first-principles boundary. -/
theorem theorem_one_at_from_first_principles_boundary
    (P : TheoremOne.MaxProblemFamily.{u})
    (h : TheoremOneCertificates P)
    (n : Nat) :
    FormalizedProof.FinalTheoremOneAtStatement P n :=
  FormalizedProof.theorem_one_at_from_radial_dependency_graph P
    h.toRadialDependencyGraph n

end FirstPrinciples
end TheoremOneManuscript
end Lollipop
