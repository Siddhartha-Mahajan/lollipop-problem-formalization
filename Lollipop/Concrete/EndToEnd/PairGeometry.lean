import Lollipop.Concrete.EndToEnd.PlanarTopology
import Lollipop.Internal.ColoredTuran.PaulsenLinearAlgebra
import Mathlib.Tactic

/-!
# Concrete pair geometry

This file proves the four robust pair-excess bounds used by the colored Turán
backend.  The proofs count connected components, not intersection
multiplicity, so every statement remains valid for tangencies, coincident
circles, and overlapping stems.
-/

noncomputable section

namespace Lollipop
namespace Concrete
namespace EndToEnd
namespace PairGeometry

open Set

/-- Compactify one primitive intersection together with infinity. -/
def hatPiece (S : Set Point) : Set Sphere2 := finiteLift S ∪ {infinity}

def pieceExcess (S : Set Point) : ℕ := componentCount (hatPiece S) - 1

/-- Close means the smaller angle between actual stem directions is at most a
right angle. -/
def Close (L M : Lollipop) : Prop :=
  0 ≤ TheoremOneEndToEnd.PaulsenLinearAlgebra.dot2
    (R2.ofPoint L.unitRadial) (R2.ofPoint M.unitRadial)

/-- The manuscript's intriguing-circle relation.  A pair is intriguing when
the two circle curves are disjoint, or when their squared center distance is at
most the sum of the squared radii.  In particular, an **external tangency is
not** intriguing: the circles meet, while the second inequality is false.

This boundary convention is essential.  The canonical Paulsen relation in the
older backend is the complement of an *open* obtuse interval and therefore
classifies an external tangency as intriguing.  That broader relation does not
satisfy the required five-component pair bound.  `Upper.lean` instead applies
the Paulsen obstruction after one uniform infinitesimal enlargement of all
radii, exactly as in the manuscript. -/
def Intriguing (L M : Lollipop) : Prop :=
  ¬ (cc L M).Nonempty ∨
    TheoremOneEndToEnd.PaulsenLinearAlgebra.distSq2
      (R2.ofPoint L.center) (R2.ofPoint M.center) ≤
        L.radius ^ 2 + M.radius ^ 2

@[simp] theorem close_symm (L M : Lollipop) : Close L M ↔ Close M L := by
  unfold Close TheoremOneEndToEnd.PaulsenLinearAlgebra.dot2
  constructor <;> intro h <;> nlinarith

@[simp] theorem intriguing_symm (L M : Lollipop) :
    Intriguing L M ↔ Intriguing M L := by
  unfold Intriguing
  rw [TheoremOneEndToEnd.PaulsenLinearAlgebra.distSq2_symm]
  have hcc : (cc M L).Nonempty ↔ (cc L M).Nonempty := by
    simp [cc, inter_comm]
  rw [hcc]
  constructor <;> rintro (hdisj | hnear)
  · exact Or.inl hdisj
  · exact Or.inr (by nlinarith)
  · exact Or.inl hdisj
  · exact Or.inr (by nlinarith)

namespace PairPort

/-- The robust pair intersection is covered by four primitive pieces, all
sharing infinity; reduced component counts are subadditive. -/
theorem pairExcess_le_piece_sum (L M : Lollipop) :
    pairExcessNat L M ≤
      pieceExcess (cc L M) + pieceExcess (rc L M) +
      pieceExcess (cr L M) + pieceExcess (rr L M) := by
  have hdecomp : hatPairIntersection L M =
      hatPiece (cc L M) ∪ hatPiece (rc L M) ∪
      hatPiece (cr L M) ∪ hatPiece (rr L M) := by
    ext x
    cases x using OnePoint.rec with
    | infty => simp [hatPairIntersection, hatPiece]
    | coe p => simp [hatPairIntersection, hatPiece, cc, rc, cr, rr,
        Lollipop.carrier, and_or_left, and_or_right, or_assoc,
        or_left_comm, or_comm]
  rw [pairExcessNat, hdecomp]
  exact connected_component_excess_union_four_le
    (infinity_mem_hatPiece (cc L M))
    (infinity_mem_hatPiece (rc L M))
    (infinity_mem_hatPiece (cr L M))
    (infinity_mem_hatPiece (rr L M))

/-- Close-pair mixed saving.  If one ray has two circle intersections, Vieta's
average-root formula places the other ray entirely outside the reverse
circle.  Otherwise both mixed counts are at most one. -/
theorem mixed_excess_sum_le_two_of_close
    {L M : Lollipop} (hclose : Close L M) :
    pieceExcess (rc L M) + pieceExcess (cr L M) ≤ 2 := by
  have hfiniteL : (rc L M).Finite := finite_ray_circle_intersection L M
  have hfiniteM : (cr L M).Finite := finite_circle_ray_intersection L M
  rw [pieceExcess, pieceExcess,
    componentCount_finiteLift_union_infinity_sub_one hfiniteL,
    componentCount_finiteLift_union_infinity_sub_one hfiniteM]
  by_cases htwo : (rc L M).ncard = 2
  · have hp : L.radius <
        dotPoint (M.center - L.center) L.unitRadial := by
      exact average_of_two_accepted_mixed_roots_gt_anchor htwo
    have hempty : cr L M = ∅ := by
      apply reverse_mixed_empty_of_two_forward_and_nonnegative_dot
        hp hclose
    simp [hempty]
  · have hL : (rc L M).ncard ≤ 1 := by
      have := circle_ray_intersection_ncard_le_two L M
      omega
    by_cases htwo' : (cr L M).ncard = 2
    · have hp : M.radius <
          dotPoint (L.center - M.center) M.unitRadial := by
        exact average_of_two_accepted_mixed_roots_gt_anchor htwo'
      have hempty : rc L M = ∅ := by
        apply reverse_mixed_empty_of_two_forward_and_nonnegative_dot
          hp ((close_symm L M).1 hclose)
      simp [hempty]
    · have hM : (cr L M).ncard ≤ 1 := by
        have := circle_ray_intersection_ncard_le_two M L
        omega
      omega

/-- In the intersecting intriguing case, each mixed primitive contributes at
most one component outside the circle--circle primitive, and two such outside
components exclude a finite ray--ray component. -/
theorem intriguing_intersecting_piece_bound
    {L M : Lollipop}
    (hintr : Intriguing L M)
    (hmeet : (cc L M).Nonempty) :
    pairExcessNat L M ≤ 4 := by
  have hnear :
      TheoremOneEndToEnd.PaulsenLinearAlgebra.distSq2
        (R2.ofPoint L.center) (R2.ofPoint M.center) ≤
          L.radius ^ 2 + M.radius ^ 2 := by
    rcases hintr with hdisj | hnear
    · exact False.elim (hdisj hmeet)
    · exact hnear
  have hdist :
      ‖M.center - L.center‖ ^ 2 ≤ L.radius ^ 2 + M.radius ^ 2 := by
    simpa [TheoremOneEndToEnd.PaulsenLinearAlgebra.distSq2,
      TheoremOneEndToEnd.PaulsenLinearAlgebra.normSq2,
      TheoremOneEndToEnd.PaulsenLinearAlgebra.dot2,
      EuclideanSpace.norm_sq_eq] using hnear
  let outRC := rc L M \ cc L M
  let outCR := cr L M \ cc L M
  have hrc : outRC.ncard ≤ 1 :=
    intriguing_mixed_outside_ncard_le_one L M hdist hmeet
  have hcr : outCR.ncard ≤ 1 :=
    intriguing_mixed_outside_ncard_le_one M L
      (by simpa [norm_sub_rev] using hdist) (by simpa [cc, inter_comm] using hmeet)
  by_cases hboth : outRC.Nonempty ∧ outCR.Nonempty
  · have hrr : rr L M = ∅ :=
      ray_ray_empty_of_both_intriguing_outside_mixed L M hdist hboth
    exact pair_excess_le_circle_plus_outside_mixed
      (EuclideanPort.circle_circle_components_le_two L M) hrc hcr hrr
  · have hone : outRC.ncard + outCR.ncard ≤ 1 := by
      rcases not_and_or.mp hboth with h | h
      · simp [Set.not_nonempty_iff_eq_empty.mp h, hcr]
      · simp [Set.not_nonempty_iff_eq_empty.mp h, hrc]
    have hrr := EuclideanPort.ray_ray_components_le_one L M
    exact pair_excess_le_circle_plus_outside_mixed_and_ray
      (EuclideanPort.circle_circle_components_le_two L M) hone hrr

end PairPort

/-- Universal `2+2+2+1` pair bound. -/
theorem pairExcess_le_seven (L M : Lollipop) : pairExcess L M ≤ 7 := by
  have h := PairPort.pairExcess_le_piece_sum L M
  have hcc := EuclideanPort.circle_circle_components_le_two L M
  have hrc := EuclideanPort.ray_circle_components_le_two L M
  have hcr := EuclideanPort.circle_ray_components_le_two L M
  have hrr := EuclideanPort.ray_ray_components_le_one L M
  exact_mod_cast (show pairExcessNat L M ≤ 7 by omega)

/-- Close-pair saving. -/
theorem pairExcess_le_five_of_close {L M : Lollipop}
    (hclose : Close L M) : pairExcess L M ≤ 5 := by
  have h := PairPort.pairExcess_le_piece_sum L M
  have hcc := EuclideanPort.circle_circle_components_le_two L M
  have hmixed := PairPort.mixed_excess_sum_le_two_of_close hclose
  have hrr := EuclideanPort.ray_ray_components_le_one L M
  exact_mod_cast (show pairExcessNat L M ≤ 5 by omega)

/-- Intriguing-pair saving.  Intersecting intriguing circles actually give the
stronger bound four; disjoint circles give five by the general primitive
count. -/
theorem pairExcess_le_five_of_intriguing {L M : Lollipop}
    (hintr : Intriguing L M) : pairExcess L M ≤ 5 := by
  by_cases hmeet : (cc L M).Nonempty
  · have h := PairPort.intriguing_intersecting_piece_bound hintr hmeet
    exact_mod_cast (h.trans (by norm_num : 4 ≤ 5))
  · have hcc : pieceExcess (cc L M) = 0 := by
      have : cc L M = ∅ := Set.not_nonempty_iff_eq_empty.mp hmeet
      simp [pieceExcess, this, hatPiece, componentCount]
    have h := PairPort.pairExcess_le_piece_sum L M
    have hrc := EuclideanPort.ray_circle_components_le_two L M
    have hcr := EuclideanPort.circle_ray_components_le_two L M
    have hrr := EuclideanPort.ray_ray_components_le_one L M
    exact_mod_cast (show pairExcessNat L M ≤ 5 by omega)

/-- Combined close/intriguing saving. -/
theorem pairExcess_le_four_of_close_intriguing {L M : Lollipop}
    (hclose : Close L M) (hintr : Intriguing L M) :
    pairExcess L M ≤ 4 := by
  by_cases hmeet : (cc L M).Nonempty
  · exact_mod_cast PairPort.intriguing_intersecting_piece_bound hintr hmeet
  · have hcc : pieceExcess (cc L M) = 0 := by
      have : cc L M = ∅ := Set.not_nonempty_iff_eq_empty.mp hmeet
      simp [pieceExcess, this, hatPiece, componentCount]
    have h := PairPort.pairExcess_le_piece_sum L M
    have hmixed := PairPort.mixed_excess_sum_le_two_of_close hclose
    have hrr := EuclideanPort.ray_ray_components_le_one L M
    exact_mod_cast (show pairExcessNat L M ≤ 3 by omega).trans (by norm_num)

end PairGeometry
end EndToEnd
end Concrete
end Lollipop
