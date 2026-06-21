import Lollipop.Internal.Manuscript.PrimitiveGeometry.LowerWitness

/-!
Concrete lower witnesses from shared anchors.

This module records a first construction-side primitive fact: if two
lollipops share their anchor, that common anchor is an actual point of the
primitive carrier intersection.  Consequently it gives a one-point finite
lower subset, and any local finite-carrier certificate turns that subset into
a rational lower bound on the pair-crossing table.
-/

namespace Lollipop
namespace TheoremOneManuscript
namespace ConstructionFormalization

open PrimitiveGeometry

/-- If two primitive lollipops share their anchor, the left anchor lies in
their primitive carrier intersection. -/
theorem left_anchor_mem_pairIntersectionSet_of_common_anchor
    {L M : EuclideanLollipop}
    (hanchor : L.anchor = M.anchor) :
    L.anchor ∈ pairIntersectionSet L M := by
  constructor
  · exact L.anchor_mem_carrier
  · simpa [hanchor] using M.anchor_mem_carrier

/-- If two primitive lollipops share their anchor, the right anchor lies in
their primitive carrier intersection. -/
theorem right_anchor_mem_pairIntersectionSet_of_common_anchor
    {L M : EuclideanLollipop}
    (hanchor : L.anchor = M.anchor) :
    M.anchor ∈ pairIntersectionSet L M := by
  simpa [hanchor] using
    left_anchor_mem_pairIntersectionSet_of_common_anchor
      (L := L) (M := M) hanchor

/-- Arrangement-indexed form of the shared-anchor primitive intersection
point. -/
theorem arrangement_left_anchor_mem_pairIntersectionSet_of_common_anchor
    {n : Nat} (A : EuclideanLollipopArrangement n)
    {i j : Fin n}
    (hanchor : (A.lollipop i).anchor = (A.lollipop j).anchor) :
    (A.lollipop i).anchor ∈ A.pairIntersectionSet i j := by
  simpa [EuclideanLollipopArrangement.pairIntersectionSet] using
    left_anchor_mem_pairIntersectionSet_of_common_anchor
      (L := A.lollipop i) (M := A.lollipop j) hanchor

/-- A single certified primitive carrier-intersection point is a one-point
finite lower subset. -/
def singleton_lower_subset_of_mem_pairIntersectionSet
    {n : Nat} {A : EuclideanLollipopArrangement n}
    {i j : Fin n} (hij : i < j) {p : R2}
    (hp : p ∈ A.pairIntersectionSet i j) :
    LocalPairCarrierLowerSubsetData A i j hij 1 where
  lowerPoints := {p}
  lowerPoints_subset := by
    intro q hq
    rw [Finset.mem_singleton] at hq
    subst q
    exact hp
  bound_le_card := by
    simp

/-- A shared anchor gives a one-point finite lower subset for that arranged
pair. -/
def common_anchor_lower_subset_one
    {n : Nat} {A : EuclideanLollipopArrangement n}
    {i j : Fin n} (hij : i < j)
    (hanchor : (A.lollipop i).anchor = (A.lollipop j).anchor) :
    LocalPairCarrierLowerSubsetData A i j hij 1 :=
  singleton_lower_subset_of_mem_pairIntersectionSet hij
    (arrangement_left_anchor_mem_pairIntersectionSet_of_common_anchor
      A hanchor)

/-- A shared anchor plus a local finite-carrier certificate gives a one-point
local lower witness. -/
def common_anchor_lower_witness_one
    {n : Nat} {A : EuclideanLollipopArrangement n}
    {pairCross : Fin n → Fin n → Rat} {i j : Fin n}
    (hij : i < j)
    (hanchor : (A.lollipop i).anchor = (A.lollipop j).anchor)
    (C : LocalPairCarrierCrossingData A pairCross i j hij) :
    LocalPairCarrierLowerWitnessData A pairCross i j hij 1 :=
  (common_anchor_lower_subset_one hij hanchor)
    |>.toLocalPairCarrierLowerWitnessData C

/-- A shared anchor plus a local finite-carrier certificate forces the
pair-crossing table to count at least one primitive carrier point. -/
theorem one_le_pair_cross_of_common_anchor
    {n : Nat} {A : EuclideanLollipopArrangement n}
    {pairCross : Fin n → Fin n → Rat} {i j : Fin n}
    (hij : i < j)
    (hanchor : (A.lollipop i).anchor = (A.lollipop j).anchor)
    (C : LocalPairCarrierCrossingData A pairCross i j hij) :
    (1 : Rat) ≤ pairCross i j :=
  (common_anchor_lower_subset_one hij hanchor).bound_le_pair_cross C

end ConstructionFormalization
end TheoremOneManuscript
end Lollipop
