import Lollipop.Internal.Manuscript.ConcreteModel

/-!
Primitive coordinate records for lollipop geometry.

This file names the geometric objects that the remaining Euclidean part of
the manuscript must construct.  It deliberately does not assert a crossing
count theorem for these sets from first principles.  Instead, it gives a
mathlib-style coordinate model for a lollipop as a circle plus a ray, then
packages the exact pairwise crossing table and incremental region data as the
remaining primitive geometric certificate.  Lean proves that such primitive
records imply the canonical upper-data interface used by Theorem 1.
-/

namespace Lollipop
namespace TheoremOneManuscript
namespace PrimitiveGeometry

universe u

abbrev R2 := TheoremOneEndToEnd.PaulsenLinearAlgebra.R2

/-- The coordinate circle with center `center` and radius `radius`, written
using the squared-distance model already used in Paulsen's formalized
appendix. -/
def circleSet (center : R2) (radius : ℝ) : Set R2 :=
  {p | TheoremOneEndToEnd.PaulsenLinearAlgebra.distSq2 p center = radius ^ 2}

/-- The half-line starting at `anchor` in direction `direction`. -/
def raySet (anchor direction : R2) : Set R2 :=
  {p | ∃ t : ℝ, 0 ≤ t ∧ p = anchor + t • direction}

/-- The base point of a ray lies on that ray. -/
theorem anchor_mem_raySet (anchor direction : R2) :
    anchor ∈ raySet anchor direction := by
  refine ⟨0, by norm_num, ?_⟩
  simp

/-- A coordinate lollipop: a circle together with a ray attached at an anchor
point on the circle, plus the normalized stem direction used by the close-pair
theorem.  The separate predicate `EuclideanLollipop.IsRadialOutward` records
the stronger manuscript condition that the ray points radially outward. -/
structure EuclideanLollipop where
  center : R2
  radius : ℝ
  radius_pos : 0 < radius
  anchor : R2
  rayDirection : R2
  rayDirection_ne_zero : rayDirection ≠ 0
  anchor_on_circle : anchor ∈ circleSet center radius
  normalizedDirection : ℝ
  normalizedDirection_nonneg : 0 ≤ normalizedDirection
  normalizedDirection_lt_one : normalizedDirection < 1

namespace EuclideanLollipop

/-- The manuscript's radial-outward stem condition: the vector from the center
to the anchor is a positive multiple of the ray direction.  The ray direction
itself may be rescaled without changing the half-line. -/
def IsRadialOutward (L : EuclideanLollipop) : Prop :=
  ∃ scale : ℝ, 0 < scale ∧ L.anchor - L.center = scale • L.rayDirection

/-- The point set of a coordinate lollipop. -/
def carrier (L : EuclideanLollipop) : Set R2 :=
  circleSet L.center L.radius ∪ raySet L.anchor L.rayDirection

/-- The circle part is contained in the lollipop carrier. -/
theorem circle_subset_carrier (L : EuclideanLollipop) :
    circleSet L.center L.radius ⊆ L.carrier := by
  intro p hp
  exact Or.inl hp

/-- The ray part is contained in the lollipop carrier. -/
theorem ray_subset_carrier (L : EuclideanLollipop) :
    raySet L.anchor L.rayDirection ⊆ L.carrier := by
  intro p hp
  exact Or.inr hp

/-- The anchor lies on the ray part of the lollipop. -/
theorem anchor_mem_ray (L : EuclideanLollipop) :
    L.anchor ∈ raySet L.anchor L.rayDirection :=
  anchor_mem_raySet L.anchor L.rayDirection

/-- The anchor lies in the lollipop carrier. -/
theorem anchor_mem_carrier (L : EuclideanLollipop) :
    L.anchor ∈ L.carrier := by
  exact Or.inl L.anchor_on_circle

end EuclideanLollipop

/-- The set of intersection points between two coordinate lollipop carriers. -/
def pairIntersectionSet (L M : EuclideanLollipop) : Set R2 :=
  L.carrier ∩ M.carrier

/-- Membership in a primitive carrier intersection is exactly one of the four
circle/ray component membership patterns. -/
theorem mem_pairIntersectionSet_iff
    {L M : EuclideanLollipop} {p : R2} :
    p ∈ pairIntersectionSet L M ↔
      (p ∈ circleSet L.center L.radius ∧
        p ∈ circleSet M.center M.radius) ∨
      (p ∈ circleSet L.center L.radius ∧
        p ∈ raySet M.anchor M.rayDirection) ∨
      (p ∈ raySet L.anchor L.rayDirection ∧
        p ∈ circleSet M.center M.radius) ∨
      (p ∈ raySet L.anchor L.rayDirection ∧
        p ∈ raySet M.anchor M.rayDirection) := by
  unfold pairIntersectionSet EuclideanLollipop.carrier
  constructor
  · intro hp
    rcases hp with ⟨hL, hM⟩
    rcases hL with hLcircle | hLray
    · rcases hM with hMcircle | hMray
      · exact Or.inl ⟨hLcircle, hMcircle⟩
      · exact Or.inr (Or.inl ⟨hLcircle, hMray⟩)
    · rcases hM with hMcircle | hMray
      · exact Or.inr (Or.inr (Or.inl ⟨hLray, hMcircle⟩))
      · exact Or.inr (Or.inr (Or.inr ⟨hLray, hMray⟩))
  · intro hp
    rcases hp with hcc | hcr | hrc | hrr
    · exact ⟨Or.inl hcc.1, Or.inl hcc.2⟩
    · exact ⟨Or.inl hcr.1, Or.inr hcr.2⟩
    · exact ⟨Or.inr hrc.1, Or.inl hrc.2⟩
    · exact ⟨Or.inr hrr.1, Or.inr hrr.2⟩

/-- Two primitive circle memberships give a point of the primitive pair
carrier intersection. -/
theorem mem_pairIntersectionSet_of_mem_circleSets
    {L M : EuclideanLollipop} {p : R2}
    (hL : p ∈ circleSet L.center L.radius)
    (hM : p ∈ circleSet M.center M.radius) :
    p ∈ pairIntersectionSet L M :=
  mem_pairIntersectionSet_iff.2 (Or.inl ⟨hL, hM⟩)

/-- A primitive left-circle/right-ray membership pair gives a point of the
primitive pair carrier intersection. -/
theorem mem_pairIntersectionSet_of_mem_circleSet_of_mem_raySet
    {L M : EuclideanLollipop} {p : R2}
    (hL : p ∈ circleSet L.center L.radius)
    (hM : p ∈ raySet M.anchor M.rayDirection) :
    p ∈ pairIntersectionSet L M :=
  mem_pairIntersectionSet_iff.2 (Or.inr (Or.inl ⟨hL, hM⟩))

/-- A primitive left-ray/right-circle membership pair gives a point of the
primitive pair carrier intersection. -/
theorem mem_pairIntersectionSet_of_mem_raySet_of_mem_circleSet
    {L M : EuclideanLollipop} {p : R2}
    (hL : p ∈ raySet L.anchor L.rayDirection)
    (hM : p ∈ circleSet M.center M.radius) :
    p ∈ pairIntersectionSet L M :=
  mem_pairIntersectionSet_iff.2
    (Or.inr (Or.inr (Or.inl ⟨hL, hM⟩)))

/-- Two primitive ray memberships give a point of the primitive pair carrier
intersection. -/
theorem mem_pairIntersectionSet_of_mem_raySets
    {L M : EuclideanLollipop} {p : R2}
    (hL : p ∈ raySet L.anchor L.rayDirection)
    (hM : p ∈ raySet M.anchor M.rayDirection) :
    p ∈ pairIntersectionSet L M :=
  mem_pairIntersectionSet_iff.2
    (Or.inr (Or.inr (Or.inr ⟨hL, hM⟩)))

/-- Pairwise carrier intersection is symmetric. -/
theorem pairIntersectionSet_symm (L M : EuclideanLollipop) :
    pairIntersectionSet L M = pairIntersectionSet M L := by
  ext p
  constructor
  · intro hp
    exact ⟨hp.2, hp.1⟩
  · intro hp
    exact ⟨hp.2, hp.1⟩

/-- A finite coordinate lollipop arrangement. -/
structure EuclideanLollipopArrangement (n : Nat) where
  lollipop : Fin n → EuclideanLollipop

namespace EuclideanLollipopArrangement

/-- The point set of the `i`-th lollipop in an arrangement. -/
def carrier {n : Nat} (A : EuclideanLollipopArrangement n) (i : Fin n) :
    Set R2 :=
  (A.lollipop i).carrier

/-- The carrier-intersection set for a pair of lollipops in an arrangement. -/
def pairIntersectionSet {n : Nat}
    (A : EuclideanLollipopArrangement n) (i j : Fin n) : Set R2 :=
  PrimitiveGeometry.pairIntersectionSet (A.lollipop i) (A.lollipop j)

/-- Arrangement-indexed carrier-intersection membership is exactly one of
the four primitive component membership patterns. -/
theorem mem_pairIntersectionSet_iff {n : Nat}
    (A : EuclideanLollipopArrangement n) {i j : Fin n} {p : R2} :
    p ∈ A.pairIntersectionSet i j ↔
      (p ∈ circleSet (A.lollipop i).center (A.lollipop i).radius ∧
        p ∈ circleSet (A.lollipop j).center (A.lollipop j).radius) ∨
      (p ∈ circleSet (A.lollipop i).center (A.lollipop i).radius ∧
        p ∈ raySet (A.lollipop j).anchor (A.lollipop j).rayDirection) ∨
      (p ∈ raySet (A.lollipop i).anchor (A.lollipop i).rayDirection ∧
        p ∈ circleSet (A.lollipop j).center (A.lollipop j).radius) ∨
      (p ∈ raySet (A.lollipop i).anchor (A.lollipop i).rayDirection ∧
        p ∈ raySet (A.lollipop j).anchor (A.lollipop j).rayDirection) :=
  PrimitiveGeometry.mem_pairIntersectionSet_iff

/-- Pairwise carrier intersection in an arrangement is symmetric. -/
theorem pairIntersectionSet_symm {n : Nat}
    (A : EuclideanLollipopArrangement n) (i j : Fin n) :
    A.pairIntersectionSet i j = A.pairIntersectionSet j i :=
  PrimitiveGeometry.pairIntersectionSet_symm (A.lollipop i) (A.lollipop j)

/-- Extract circle centers from a coordinate lollipop arrangement. -/
def center {n : Nat} (A : EuclideanLollipopArrangement n) (i : Fin n) : R2 :=
  (A.lollipop i).center

/-- Extract radii from a coordinate lollipop arrangement. -/
def radius {n : Nat} (A : EuclideanLollipopArrangement n) (i : Fin n) : ℝ :=
  (A.lollipop i).radius

/-- Extract normalized stem directions from a coordinate lollipop arrangement. -/
def normalizedDirection {n : Nat}
    (A : EuclideanLollipopArrangement n) (i : Fin n) : ℝ :=
  (A.lollipop i).normalizedDirection

theorem radius_pos {n : Nat} (A : EuclideanLollipopArrangement n)
    (i : Fin n) :
    0 < A.radius i :=
  (A.lollipop i).radius_pos

theorem normalizedDirection_nonneg {n : Nat}
    (A : EuclideanLollipopArrangement n) (i : Fin n) :
    0 ≤ A.normalizedDirection i :=
  (A.lollipop i).normalizedDirection_nonneg

theorem normalizedDirection_lt_one {n : Nat}
    (A : EuclideanLollipopArrangement n) (i : Fin n) :
    A.normalizedDirection i < 1 :=
  (A.lollipop i).normalizedDirection_lt_one

end EuclideanLollipopArrangement

/-- A local carrier-intersection certificate for one ordered pair `i < j` in a
primitive coordinate lollipop arrangement.  This is the one-pair version of
`PairwiseCarrierCrossingData`, intended for first-principles Euclidean
calculations that identify one finite crossing set at a time. -/
structure LocalPairCarrierCrossingData
    {n : Nat} (A : EuclideanLollipopArrangement n)
    (cross : Fin n → Fin n → Rat) (i j : Fin n) (hij : i < j) where
  crossingPoints : Finset R2
  crossingPoints_spec :
    (crossingPoints : Set R2) = A.pairIntersectionSet i j
  cross_eq_card :
    cross i j = (crossingPoints.card : Rat)

/-- A finite carrier-intersection certificate for the pairwise crossing table
of one primitive coordinate lollipop arrangement.  In a fully first-principles
Euclidean proof, `crossingPoints_spec` is where the circle/ray intersection
calculation would identify the actual finite set of crossings. -/
structure PairwiseCarrierCrossingData
    {n : Nat} (A : EuclideanLollipopArrangement n)
    (cross : Fin n → Fin n → Rat) where
  crossingPoints : ∀ i j : Fin n, i < j → Finset R2
  crossingPoints_spec :
    ∀ i j : Fin n, ∀ hij : i < j,
      (crossingPoints i j hij : Set R2) = A.pairIntersectionSet i j
  cross_eq_card :
    ∀ i j : Fin n, ∀ hij : i < j,
      cross i j = ((crossingPoints i j hij).card : Rat)

namespace PairwiseCarrierCrossingData

/-- Assemble local one-pair carrier-intersection certificates into the global
pairwise crossing-data structure expected by the theorem stack. -/
noncomputable def ofLocal
    {n : Nat} {A : EuclideanLollipopArrangement n}
    {cross : Fin n → Fin n → Rat}
    (loc :
      ∀ i j : Fin n, ∀ hij : i < j,
        LocalPairCarrierCrossingData A cross i j hij) :
    PairwiseCarrierCrossingData A cross where
  crossingPoints := fun i j hij => (loc i j hij).crossingPoints
  crossingPoints_spec := by
    intro i j hij
    exact (loc i j hij).crossingPoints_spec
  cross_eq_card := by
    intro i j hij
    exact (loc i j hij).cross_eq_card

end PairwiseCarrierCrossingData

/-- Primitive upper geometric data for a problem family.  Compared with
`CanonicalExactUpperGeometryIncrementalData`, this names the actual coordinate
lollipops whose centers, radii, and stem directions feed the canonical
case-bound table.  The difficult remaining Euclidean certificate is exactly
the pairwise crossing-count table `cross_le_case`, together with the
incremental region data for those crossings. -/
structure PrimitiveExactUpperGeometryData
    (P : TheoremOne.ProblemFamily.{u}) where
  arrangement :
    ∀ n : Nat, P.Arrangement n → EuclideanLollipopArrangement n
  cross :
    ∀ n : Nat, P.Arrangement n → Fin n → Fin n → Rat
  cross_le_case :
    ∀ n : Nat, ∀ A : P.Arrangement n, ∀ i j : Fin n, i < j →
      cross n A i j ≤
        TheoremOneEndToEnd.canonicalCrossingCaseBound
          (fun k => (arrangement n A).normalizedDirection k)
          (fun k => (arrangement n A).center k)
          (fun k => (arrangement n A).radius k) i j
  region_increment :
    ∀ n : Nat, ∀ A : P.Arrangement n,
      OrderedIncrementalPairRegionData n (P.region n A) (cross n A)

namespace PrimitiveExactUpperGeometryData

/-- Primitive coordinate lollipop data imply the canonical exact upper
geometry interface used by the manuscript theorem stack. -/
def toCanonicalExactUpperGeometryIncrementalData
    {P : TheoremOne.ProblemFamily.{u}}
    (h : PrimitiveExactUpperGeometryData P) :
    CanonicalExactUpperGeometryIncrementalData P where
  center := fun n A i => (h.arrangement n A).center i
  radius := fun n A i => (h.arrangement n A).radius i
  radius_pos := by
    intro n A i
    exact (h.arrangement n A).radius_pos i
  direction := fun n A i => (h.arrangement n A).normalizedDirection i
  direction_nonneg := by
    intro n A i
    exact (h.arrangement n A).normalizedDirection_nonneg i
  direction_lt_one := by
    intro n A i
    exact (h.arrangement n A).normalizedDirection_lt_one i
  cross := h.cross
  cross_le_case := h.cross_le_case
  region_increment := h.region_increment

end PrimitiveExactUpperGeometryData

/-- Stronger primitive upper data where the pairwise crossing table is also
certified by finite intersection sets of the lollipop carriers. -/
structure PrimitiveCarrierCertifiedExactUpperGeometryData
    (P : TheoremOne.ProblemFamily.{u}) where
  arrangement :
    ∀ n : Nat, P.Arrangement n → EuclideanLollipopArrangement n
  cross :
    ∀ n : Nat, P.Arrangement n → Fin n → Fin n → Rat
  pairwise_crossings :
    ∀ n : Nat, ∀ A : P.Arrangement n,
      PairwiseCarrierCrossingData (arrangement n A) (cross n A)
  cross_le_case :
    ∀ n : Nat, ∀ A : P.Arrangement n, ∀ i j : Fin n, i < j →
      cross n A i j ≤
        TheoremOneEndToEnd.canonicalCrossingCaseBound
          (fun k => (arrangement n A).normalizedDirection k)
          (fun k => (arrangement n A).center k)
          (fun k => (arrangement n A).radius k) i j
  region_increment :
    ∀ n : Nat, ∀ A : P.Arrangement n,
      OrderedIncrementalPairRegionData n (P.region n A) (cross n A)

namespace PrimitiveCarrierCertifiedExactUpperGeometryData

/-- Forget the explicit finite carrier-intersection witnesses after retaining
the exact pairwise crossing table they certify. -/
def toPrimitiveExactUpperGeometryData
    {P : TheoremOne.ProblemFamily.{u}}
    (h : PrimitiveCarrierCertifiedExactUpperGeometryData P) :
    PrimitiveExactUpperGeometryData P where
  arrangement := h.arrangement
  cross := h.cross
  cross_le_case := h.cross_le_case
  region_increment := h.region_increment

/-- Carrier-certified primitive data imply the canonical exact upper geometry
interface used by the theorem stack. -/
def toCanonicalExactUpperGeometryIncrementalData
    {P : TheoremOne.ProblemFamily.{u}}
    (h : PrimitiveCarrierCertifiedExactUpperGeometryData P) :
    CanonicalExactUpperGeometryIncrementalData P :=
  h.toPrimitiveExactUpperGeometryData.toCanonicalExactUpperGeometryIncrementalData

end PrimitiveCarrierCertifiedExactUpperGeometryData

end PrimitiveGeometry
end TheoremOneManuscript
end Lollipop
