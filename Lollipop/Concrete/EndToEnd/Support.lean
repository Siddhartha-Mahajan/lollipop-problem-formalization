import Lollipop.Concrete.EndToEnd.Compactification
import Mathlib.Analysis.Convex.Segment
import Mathlib.Data.Finset.Card
import Mathlib.Tactic

/-!
# Shared geometric and finite-component support

This module isolates low-level Euclidean facts used by both the arbitrary
upper bound and the generic lower construction.  The declarations in
`EuclideanPort` are narrow API ports: their proofs are elementary coordinate
arguments (linear equations for rays and quadratic equations for circles).
-/

noncomputable section

namespace Lollipop
namespace Concrete
namespace EndToEnd

open Set BigOperators

/-- Determinant and dot product in displayed coordinates. -/
def detPoint (u v : Point) : ℝ := u 0 * v 1 - u 1 * v 0

def dotPoint (u v : Point) : ℝ := u 0 * v 0 + u 1 * v 1

@[simp] theorem detPoint_skew (u v : Point) :
    detPoint v u = -detPoint u v := by
  unfold detPoint
  ring

@[simp] theorem dotPoint_comm (u v : Point) :
    dotPoint v u = dotPoint u v := by
  unfold dotPoint
  ring

/-- Primitive crossing sets. -/
def cc (L M : Lollipop) : Set Point := L.circle ∩ M.circle
def cr (L M : Lollipop) : Set Point := L.circle ∩ M.stem
def rc (L M : Lollipop) : Set Point := L.stem ∩ M.circle
def rr (L M : Lollipop) : Set Point := L.stem ∩ M.stem

def pairCrossingSet (L M : Lollipop) : Set Point := L.carrier ∩ M.carrier

def pairCrossingCount (L M : Lollipop) : ℕ :=
  (pairCrossingSet L M).ncard

@[simp] theorem pairCrossingSet_decompose (L M : Lollipop) :
    pairCrossingSet L M = cc L M ∪ rc L M ∪ cr L M ∪ rr L M := by
  ext x
  simp [pairCrossingSet, cc, cr, rc, rr, Lollipop.carrier,
    and_or_left, and_or_right, or_assoc, or_left_comm, or_comm]

/-- Transversality predicates in coordinates. -/
def CircleCircleTransverseAt (L M : Lollipop) (x : Point) : Prop :=
  detPoint (x - L.center) (x - M.center) ≠ 0

def StemCircleTransverseAt (L M : Lollipop) (x : Point) : Prop :=
  dotPoint L.radial (x - M.center) ≠ 0

def StemStemTransverse (L M : Lollipop) : Prop :=
  detPoint L.radial M.radial ≠ 0

structure PrimitivePairwiseTransverse (L M : Lollipop) : Prop where
  cc : ∀ x, x ∈ cc L M → CircleCircleTransverseAt L M x
  cr : ∀ x, x ∈ cr L M → StemCircleTransverseAt M L x
  rc : ∀ x, x ∈ rc L M → StemCircleTransverseAt L M x
  rr : (rr L M).Nonempty → StemStemTransverse L M

/-- The stem is convex. -/
theorem stem_convex (L : Lollipop) : Convex ℝ L.stem := by
  rw [L.stem_eq_image_Ici]
  exact (convex_Ici.linear_image
    (LinearMap.id.smulRight L.radial)).vadd L.center

/-- Every compactified carrier is compact. -/
theorem isCompact_hatCarrier (L : Lollipop) : IsCompact (hatCarrier L) := by
  simpa [hatCarrier, finiteLift, finitePoint, infinity] using
    OnePoint.isCompact_coe_image_union_infty_of_isClosed L.isClosed_carrier

/-- Every finite compactified arrangement union is compact. -/
theorem isCompact_hatOccupied {n : ℕ} (A : Arrangement n) :
    IsCompact (hatOccupied A) := by
  classical
  exact (isCompact_iUnion_finite fun i : Fin n => isCompact_hatCarrier (A i)).union
    isCompact_singleton

/-- A finite set plus infinity has one component per finite point and one at
infinity. -/
theorem componentCount_finiteLift_union_infinity_sub_one
    {S : Set Point} (hS : S.Finite) :
    componentCount (finiteLift S ∪ {infinity}) - 1 = S.ncard := by
  let e : S ≃ finiteLift S :=
    { toFun := fun x => ⟨finitePoint x, ⟨x, x.property, rfl⟩⟩
      invFun := fun y => by
        rcases y with ⟨_, x, hx, rfl⟩
        exact ⟨x, hx⟩
      left_inv := by intro x; rfl
      right_inv := by rintro ⟨_, x, hx, rfl⟩; rfl }
  have hdisc : DiscreteTopology S := Finite.to_discreteTopology
  have hcomponents :
      ConnectedComponents (finiteLift S ∪ {infinity}) ≃ Option S :=
    connectedComponents_finite_chart_union_infinity_equiv hS e
  unfold componentCount
  rw [Nat.card_congr hcomponents, Nat.card_option, Nat.card_coe_set_eq_ncard hS]
  omega


namespace EuclideanPort

/-- Two distinct planar circles meet in at most two points; equal circles form
one connected primitive component. -/
theorem circle_circle_components_le_two (L M : Lollipop) :
    componentCount (finiteLift (cc L M) ∪ {infinity}) - 1 ≤ 2 := by
  by_cases hsame : L.circle = M.circle
  · have hconn : IsConnected (finiteLift (cc L M)) := by
      simpa [cc, hsame] using
        L.isConnected_circle.image finitePoint OnePoint.continuous_coe.continuousOn
    exact component_excess_union_infinity_le_one hconn
  · have hfinite : (cc L M).Finite := by
      exact finite_circle_intersection_of_ne hsame
    have hcard : (cc L M).ncard ≤ 2 :=
      circle_intersection_ncard_le_two L.center M.center L.radius M.radius hsame
    rw [componentCount_finiteLift_union_infinity_sub_one hfinite]
    exact hcard

/-- A circle and a radial ray meet in at most two connected components. -/
theorem circle_ray_components_le_two (L M : Lollipop) :
    componentCount (finiteLift (cr L M) ∪ {infinity}) - 1 ≤ 2 := by
  have hfinite : (cr L M).Finite :=
    finite_circle_ray_intersection L M
  have hcard : (cr L M).ncard ≤ 2 :=
    circle_ray_intersection_ncard_le_two L M
  rw [componentCount_finiteLift_union_infinity_sub_one hfinite]
  exact hcard

/-- Symmetric mixed bound. -/
theorem ray_circle_components_le_two (L M : Lollipop) :
    componentCount (finiteLift (rc L M) ∪ {infinity}) - 1 ≤ 2 := by
  simpa [rc, cr, inter_comm] using circle_ray_components_le_two M L

/-- Two rays have at most one finite connected component after removing the
common infinity component, including overlapping collinear rays. -/
theorem ray_ray_components_le_one (L M : Lollipop) :
    componentCount (finiteLift (rr L M) ∪ {infinity}) - 1 ≤ 1 := by
  have hconv : Convex ℝ (rr L M) := (stem_convex L).inter (stem_convex M)
  exact component_excess_of_convex_finite_chart_le_one hconv

/-- A finite transverse primitive pair has one connected component for every
finite crossing, plus infinity. -/
theorem pairExcess_eq_ncard_of_transverse
    {L M : Lollipop}
    (hfinite : (pairCrossingSet L M).Finite)
    (htrans : PrimitivePairwiseTransverse L M)
    (hnoTriple :
      Set.PairwiseDisjoint (fun k : Fin 4 =>
        match k with
        | 0 => cc L M
        | 1 => rc L M
        | 2 => cr L M
        | 3 => rr L M)) :
    pairExcessNat L M = pairCrossingCount L M := by
  have hhat : hatPairIntersection L M =
      finiteLift (pairCrossingSet L M) ∪ {infinity} := by
    ext x
    cases x using OnePoint.rec with
    | infty => simp [hatPairIntersection]
    | coe p => simp [hatPairIntersection, pairCrossingSet]
  rw [pairExcessNat, hhat,
    componentCount_finiteLift_union_infinity_sub_one hfinite]
  rfl

/-- A transverse circle--circle intersection is isolated. -/
theorem isolated_cc_of_transverse
    {L M : Lollipop} {x : Point}
    (hx : x ∈ cc L M) (h : CircleCircleTransverseAt L M x) :
    IsolatedPoint (cc L M) x := by
  exact isolated_zero_of_regular_level_pair_circle_equations hx h

/-- A transverse mixed intersection is isolated. -/
theorem isolated_rc_of_transverse
    {L M : Lollipop} {x : Point}
    (hx : x ∈ rc L M) (h : StemCircleTransverseAt L M x) :
    IsolatedPoint (rc L M) x := by
  exact isolated_zero_of_regular_ray_circle_equation hx h

/-- A transverse ray--ray point is isolated. -/
theorem isolated_rr_of_transverse
    {L M : Lollipop} {x : Point}
    (hx : x ∈ rr L M) (h : StemStemTransverse L M) :
    IsolatedPoint (rr L M) x := by
  exact isolated_intersection_of_nonparallel_affine_lines hx h

end EuclideanPort

/-- Finite unions of connected sets sharing a common point are connected. -/
theorem isConnected_iUnion_of_common
    {ι X : Type*} [Fintype ι] [TopologicalSpace X]
    {S : ι → Set X}
    (hS : ∀ i, IsConnected (S i))
    (p : X) (hp : ∀ i, p ∈ S i) (i0 : ι) :
    IsConnected (⋃ i, S i) := by
  refine ⟨⟨p, Set.mem_iUnion_of_mem i0 (hp i0)⟩, ?_⟩
  exact isPreconnected_iUnion (fun i => (hS i).isPreconnected)
    (fun i => ⟨p, hp i0, hp i⟩)

end EndToEnd
end Concrete
end Lollipop
