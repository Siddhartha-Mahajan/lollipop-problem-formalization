import Lollipop.Internal.Manuscript.ExplicitInputs.KarlssonOEIS
import Lollipop.Internal.Manuscript.PrimitiveGeometry.ComponentBounds

/-!
Geometry-facing consequences of the exact OEIS/Karlsson base certificate.

`KarlssonOEIS.lean` records the four coordinate lollipops and names the finite
carrier-intersection certificate type.  This file unwraps that certificate
into the six concrete cardinality obligations for the displayed
`5,7,7,7,7,7` base table, and records easy noncoincidence facts that follow
from the visible radii.
-/

namespace Lollipop
namespace TheoremOneManuscript
namespace ExplicitInputs

open PrimitiveGeometry
open TheoremOneEndToEnd.PaulsenLinearAlgebra

/-- Determinant of two bearing direction vectors. -/
theorem det2_angleDirection (theta phi : ℝ) :
    det2 (angleDirection theta) (angleDirection phi) =
      Real.sin (phi - theta) := by
  unfold det2 angleDirection point2
  rw [Real.sin_sub]
  ring

/-- The recorded normalized OEIS directions make the exceptional base pair
`(Q0,Q1)` a close pair in the cyclic direction relation. -/
theorem karlssonOEISBase_zero_one_cyclicClose :
    TheoremOneEndToEnd.CloseDirection.cyclicClose
      (fun i : Fin 4 => karlssonOEISBaseArrangement.normalizedDirection i)
      (0 : Fin 4) (1 : Fin 4) := by
  unfold TheoremOneEndToEnd.CloseDirection.cyclicClose
    TheoremOneEndToEnd.CloseDirection.cyclicClosePair
  right
  let eps : ℝ := (1 / 100 : ℝ) / (2 * Real.pi)
  have heps_le_quarter : eps ≤ 1 / 4 := by
    dsimp [eps]
    have hden : 0 < 2 * Real.pi := by positivity
    rw [div_le_iff₀ hden]
    nlinarith [Real.pi_gt_three]
  have hdiff :
      karlssonOEISBaseArrangement.normalizedDirection (0 : Fin 4) -
        karlssonOEISBaseArrangement.normalizedDirection (1 : Fin 4) =
      -(1 - eps) := by
    dsimp [eps]
    simp [EuclideanLollipopArrangement.normalizedDirection,
      karlssonOEISBaseArrangement, karlssonOEISQ0, karlssonOEISQ1,
      EuclideanLollipop.fromAnchor, EuclideanLollipop.fromCenter,
      normalizedMinusPoint01]
  rw [hdiff, abs_neg]
  have hnonneg : 0 ≤ 1 - eps := by linarith
  rw [abs_of_nonneg hnonneg]
  linarith

/-- The OEIS base pair `(Q0,Q2)` is not close by its recorded normalized
directions. -/
theorem karlssonOEISBase_zero_two_not_cyclicClose :
    ¬ TheoremOneEndToEnd.CloseDirection.cyclicClose
      (fun i : Fin 4 => karlssonOEISBaseArrangement.normalizedDirection i)
      (0 : Fin 4) (2 : Fin 4) := by
  apply TheoremOneEndToEnd.CloseDirection.not_cyclicClose_of_abs_between
  · norm_num [EuclideanLollipopArrangement.normalizedDirection,
      karlssonOEISBaseArrangement, karlssonOEISQ0, karlssonOEISQ2,
      EuclideanLollipop.fromAnchor]
  · norm_num [EuclideanLollipopArrangement.normalizedDirection,
      karlssonOEISBaseArrangement, karlssonOEISQ0, karlssonOEISQ2,
      EuclideanLollipop.fromAnchor]

/-- The OEIS base pair `(Q0,Q3)` is not close by its recorded normalized
directions. -/
theorem karlssonOEISBase_zero_three_not_cyclicClose :
    ¬ TheoremOneEndToEnd.CloseDirection.cyclicClose
      (fun i : Fin 4 => karlssonOEISBaseArrangement.normalizedDirection i)
      (0 : Fin 4) (3 : Fin 4) := by
  apply TheoremOneEndToEnd.CloseDirection.not_cyclicClose_of_abs_between
  · norm_num [EuclideanLollipopArrangement.normalizedDirection,
      karlssonOEISBaseArrangement, karlssonOEISQ0, karlssonOEISQ3,
      EuclideanLollipop.fromAnchor]
  · norm_num [EuclideanLollipopArrangement.normalizedDirection,
      karlssonOEISBaseArrangement, karlssonOEISQ0, karlssonOEISQ3,
      EuclideanLollipop.fromAnchor]

/-- The OEIS base pair `(Q2,Q3)` is not close by its recorded normalized
directions. -/
theorem karlssonOEISBase_two_three_not_cyclicClose :
    ¬ TheoremOneEndToEnd.CloseDirection.cyclicClose
      (fun i : Fin 4 => karlssonOEISBaseArrangement.normalizedDirection i)
      (2 : Fin 4) (3 : Fin 4) := by
  apply TheoremOneEndToEnd.CloseDirection.not_cyclicClose_of_abs_between
  · norm_num [EuclideanLollipopArrangement.normalizedDirection,
      karlssonOEISBaseArrangement, karlssonOEISQ2, karlssonOEISQ3,
      EuclideanLollipop.fromAnchor]
  · norm_num [EuclideanLollipopArrangement.normalizedDirection,
      karlssonOEISBaseArrangement, karlssonOEISQ2, karlssonOEISQ3,
      EuclideanLollipop.fromAnchor]

/-- The small negative-direction normalization error in `Q1` is below
`1/15`, which is enough for the remaining OEIS non-close direction checks. -/
private theorem karlssonOEISBase_q1_epsilon_lt_one_fifteenth :
    (1 / 100 : ℝ) / (2 * Real.pi) < 1 / 15 := by
  have hden : 0 < 2 * Real.pi := by positivity
  rw [div_lt_iff₀ hden]
  nlinarith [Real.pi_gt_three]

/-- The OEIS base pair `(Q1,Q2)` is not close by its recorded normalized
directions. -/
theorem karlssonOEISBase_one_two_not_cyclicClose :
    ¬ TheoremOneEndToEnd.CloseDirection.cyclicClose
      (fun i : Fin 4 => karlssonOEISBaseArrangement.normalizedDirection i)
      (1 : Fin 4) (2 : Fin 4) := by
  let eps : ℝ := (1 / 100 : ℝ) / (2 * Real.pi)
  have heps_lt : eps < 1 / 15 := by
    simpa [eps] using karlssonOEISBase_q1_epsilon_lt_one_fifteenth
  have heps_pos : 0 < eps := by positivity
  have hdiff :
      karlssonOEISBaseArrangement.normalizedDirection (1 : Fin 4) -
        karlssonOEISBaseArrangement.normalizedDirection (2 : Fin 4) =
      19 / 60 - eps := by
    dsimp [eps]
    simp [EuclideanLollipopArrangement.normalizedDirection,
      karlssonOEISBaseArrangement, karlssonOEISQ1, karlssonOEISQ2,
      EuclideanLollipop.fromCenter, EuclideanLollipop.fromAnchor,
      normalizedMinusPoint01]
    ring
  have habs :
      |karlssonOEISBaseArrangement.normalizedDirection (1 : Fin 4) -
        karlssonOEISBaseArrangement.normalizedDirection (2 : Fin 4)| =
      19 / 60 - eps := by
    rw [hdiff]
    rw [abs_of_nonneg]
    linarith
  apply TheoremOneEndToEnd.CloseDirection.not_cyclicClose_of_abs_between
  · rw [habs]
    linarith
  · rw [habs]
    linarith

/-- The OEIS base pair `(Q1,Q3)` is not close by its recorded normalized
directions. -/
theorem karlssonOEISBase_one_three_not_cyclicClose :
    ¬ TheoremOneEndToEnd.CloseDirection.cyclicClose
      (fun i : Fin 4 => karlssonOEISBaseArrangement.normalizedDirection i)
      (1 : Fin 4) (3 : Fin 4) := by
  let eps : ℝ := (1 / 100 : ℝ) / (2 * Real.pi)
  have heps_lt : eps < 1 / 15 := by
    simpa [eps] using karlssonOEISBase_q1_epsilon_lt_one_fifteenth
  have heps_pos : 0 < eps := by positivity
  have hdiff :
      karlssonOEISBaseArrangement.normalizedDirection (1 : Fin 4) -
        karlssonOEISBaseArrangement.normalizedDirection (3 : Fin 4) =
      11 / 15 - eps := by
    dsimp [eps]
    simp [EuclideanLollipopArrangement.normalizedDirection,
      karlssonOEISBaseArrangement, karlssonOEISQ1, karlssonOEISQ3,
      EuclideanLollipop.fromCenter, EuclideanLollipop.fromAnchor,
      normalizedMinusPoint01]
    ring
  have habs :
      |karlssonOEISBaseArrangement.normalizedDirection (1 : Fin 4) -
        karlssonOEISBaseArrangement.normalizedDirection (3 : Fin 4)| =
      11 / 15 - eps := by
    rw [hdiff]
    rw [abs_of_nonneg]
    linarith
  apply TheoremOneEndToEnd.CloseDirection.not_cyclicClose_of_abs_between
  · rw [habs]
    linarith
  · rw [habs]
    linarith

/-- The same exceptional OEIS base pair is not intriguing: its two circles
satisfy Paulsen's strict obtuse-intersection distance condition. -/
theorem karlssonOEISQ0_Q1_circleObtuseCondition :
    circleObtuseCondition karlssonOEISQ0.radius karlssonOEISQ1.radius
      karlssonOEISQ0.center karlssonOEISQ1.center := by
  unfold circleObtuseCondition distSq2 normSq2 dot2
  norm_num [karlssonOEISQ0, karlssonOEISQ1,
    EuclideanLollipop.fromAnchor, EuclideanLollipop.fromCenter,
    angleDirection, point2]

/-- Pair-level form: `(Q0,Q1)` is not intriguing. -/
theorem karlssonOEISQ0_Q1_not_circleIntriguingPair :
    ¬ circleIntriguingPair karlssonOEISQ0.radius karlssonOEISQ1.radius
      karlssonOEISQ0.center karlssonOEISQ1.center := by
  classical
  exact not_not.mpr karlssonOEISQ0_Q1_circleObtuseCondition

/-- Arrangement-level form: the exact OEIS base pair `(0,1)` is not
intriguing for the canonical circle relation. -/
theorem karlssonOEISBase_zero_one_not_circleIntriguing :
    ¬ circleIntriguing
      (fun i : Fin 4 => karlssonOEISBaseArrangement.center i)
      (fun i : Fin 4 => karlssonOEISBaseArrangement.radius i)
      (0 : Fin 4) (1 : Fin 4) := by
  simpa [circleIntriguing, EuclideanLollipopArrangement.center,
    EuclideanLollipopArrangement.radius] using
    karlssonOEISQ0_Q1_not_circleIntriguingPair

/-- The finite carrier-intersection certificate identifies every certified
pair's finite set cardinality with the Karlsson base table. -/
theorem KarlssonOEISBaseCoordinateCrossingCertificate.crossingPoints_card_eq_base
    (C : KarlssonOEISBaseCoordinateCrossingCertificate)
    {i j : Fin 4} (hij : i < j) :
    ((C.pairwise_crossings.crossingPoints i j hij).card : Rat) =
      karlssonBasePairCrossing i j := by
  exact (C.pairwise_crossings.cross_eq_card i j hij).symm

/-- The exceptional base pair has exactly five certified carrier-intersection
points. -/
theorem KarlssonOEISBaseCoordinateCrossingCertificate.card_zero_one
    (C : KarlssonOEISBaseCoordinateCrossingCertificate) :
    (C.pairwise_crossings.crossingPoints (0 : Fin 4) (1 : Fin 4)
      (by decide)).card = 5 := by
  have h :=
    C.crossingPoints_card_eq_base
      (i := (0 : Fin 4)) (j := (1 : Fin 4)) (by decide)
  norm_num at h
  exact_mod_cast h

/-- The `(0,2)` base pair has exactly seven certified carrier-intersection
points. -/
theorem KarlssonOEISBaseCoordinateCrossingCertificate.card_zero_two
    (C : KarlssonOEISBaseCoordinateCrossingCertificate) :
    (C.pairwise_crossings.crossingPoints (0 : Fin 4) (2 : Fin 4)
      (by decide)).card = 7 := by
  have h :=
    C.crossingPoints_card_eq_base
      (i := (0 : Fin 4)) (j := (2 : Fin 4)) (by decide)
  norm_num at h
  exact_mod_cast h

/-- The `(0,3)` base pair has exactly seven certified carrier-intersection
points. -/
theorem KarlssonOEISBaseCoordinateCrossingCertificate.card_zero_three
    (C : KarlssonOEISBaseCoordinateCrossingCertificate) :
    (C.pairwise_crossings.crossingPoints (0 : Fin 4) (3 : Fin 4)
      (by decide)).card = 7 := by
  have h :=
    C.crossingPoints_card_eq_base
      (i := (0 : Fin 4)) (j := (3 : Fin 4)) (by decide)
  norm_num at h
  exact_mod_cast h

/-- The `(1,2)` base pair has exactly seven certified carrier-intersection
points. -/
theorem KarlssonOEISBaseCoordinateCrossingCertificate.card_one_two
    (C : KarlssonOEISBaseCoordinateCrossingCertificate) :
    (C.pairwise_crossings.crossingPoints (1 : Fin 4) (2 : Fin 4)
      (by decide)).card = 7 := by
  have h :=
    C.crossingPoints_card_eq_base
      (i := (1 : Fin 4)) (j := (2 : Fin 4)) (by decide)
  norm_num at h
  exact_mod_cast h

/-- The `(1,3)` base pair has exactly seven certified carrier-intersection
points. -/
theorem KarlssonOEISBaseCoordinateCrossingCertificate.card_one_three
    (C : KarlssonOEISBaseCoordinateCrossingCertificate) :
    (C.pairwise_crossings.crossingPoints (1 : Fin 4) (3 : Fin 4)
      (by decide)).card = 7 := by
  have h :=
    C.crossingPoints_card_eq_base
      (i := (1 : Fin 4)) (j := (3 : Fin 4)) (by decide)
  norm_num at h
  exact_mod_cast h

/-- The `(2,3)` base pair has exactly seven certified carrier-intersection
points. -/
theorem KarlssonOEISBaseCoordinateCrossingCertificate.card_two_three
    (C : KarlssonOEISBaseCoordinateCrossingCertificate) :
    (C.pairwise_crossings.crossingPoints (2 : Fin 4) (3 : Fin 4)
      (by decide)).card = 7 := by
  have h :=
    C.crossingPoints_card_eq_base
      (i := (2 : Fin 4)) (j := (3 : Fin 4)) (by decide)
  norm_num at h
  exact_mod_cast h

/-- Proposition bundling the six displayed OEIS/Karlsson base-coordinate
finite carrier-intersection cardinalities. -/
def KarlssonOEISBaseCoordinateCrossingCertificate.SixPairCardinalities
    (C : KarlssonOEISBaseCoordinateCrossingCertificate) : Prop :=
  (C.pairwise_crossings.crossingPoints (0 : Fin 4) (1 : Fin 4)
    (by decide)).card = 5 ∧
  (C.pairwise_crossings.crossingPoints (0 : Fin 4) (2 : Fin 4)
    (by decide)).card = 7 ∧
  (C.pairwise_crossings.crossingPoints (0 : Fin 4) (3 : Fin 4)
    (by decide)).card = 7 ∧
  (C.pairwise_crossings.crossingPoints (1 : Fin 4) (2 : Fin 4)
    (by decide)).card = 7 ∧
  (C.pairwise_crossings.crossingPoints (1 : Fin 4) (3 : Fin 4)
    (by decide)).card = 7 ∧
  (C.pairwise_crossings.crossingPoints (2 : Fin 4) (3 : Fin 4)
    (by decide)).card = 7

/-- The exact OEIS/Karlsson base-coordinate certificate is equivalent, at
the six displayed unordered pairs, to the visible `5,7,7,7,7,7` finite
carrier-intersection cardinalities. -/
theorem KarlssonOEISBaseCoordinateCrossingCertificate.six_pair_cardinalities
    (C : KarlssonOEISBaseCoordinateCrossingCertificate) :
    C.SixPairCardinalities := by
  exact ⟨C.card_zero_one, C.card_zero_two, C.card_zero_three,
    C.card_one_two, C.card_one_three, C.card_two_three⟩

/-- Six independent pair certificates imply the bundled six displayed
OEIS/Karlsson cardinalities after assembly into the all-pairs certificate. -/
theorem KarlssonOEISBaseSixPairCoordinateCrossingCertificate.six_pair_cardinalities
    (C : KarlssonOEISBaseSixPairCoordinateCrossingCertificate) :
    C.toCoordinateCrossingCertificate.SixPairCardinalities :=
  C.toCoordinateCrossingCertificate.six_pair_cardinalities

/-- The OEIS `Q0` and `Q1` lifted circles are different, already because
their radii are different. -/
theorem karlssonOEISQ0_Q1_spheres_distinct :
    euclideanSphere karlssonOEISQ0.center karlssonOEISQ0.radius ≠
      euclideanSphere karlssonOEISQ1.center karlssonOEISQ1.radius := by
  apply euclideanSphere_ne_of_radius_ne
  norm_num [karlssonOEISQ0, karlssonOEISQ1,
    EuclideanLollipop.fromAnchor, EuclideanLollipop.fromCenter]

/-- The OEIS `Q0` and `Q2` lifted circles are different, already because
their radii are different. -/
theorem karlssonOEISQ0_Q2_spheres_distinct :
    euclideanSphere karlssonOEISQ0.center karlssonOEISQ0.radius ≠
      euclideanSphere karlssonOEISQ2.center karlssonOEISQ2.radius := by
  apply euclideanSphere_ne_of_radius_ne
  norm_num [karlssonOEISQ0, karlssonOEISQ2,
    EuclideanLollipop.fromAnchor]

/-- The OEIS `Q0` and `Q3` lifted circles are different, already because
their radii are different. -/
theorem karlssonOEISQ0_Q3_spheres_distinct :
    euclideanSphere karlssonOEISQ0.center karlssonOEISQ0.radius ≠
      euclideanSphere karlssonOEISQ3.center karlssonOEISQ3.radius := by
  apply euclideanSphere_ne_of_radius_ne
  norm_num [karlssonOEISQ0, karlssonOEISQ3,
    EuclideanLollipop.fromAnchor]

/-- The OEIS `Q1` and `Q2` lifted circles are different, already because
their radii are different. -/
theorem karlssonOEISQ1_Q2_spheres_distinct :
    euclideanSphere karlssonOEISQ1.center karlssonOEISQ1.radius ≠
      euclideanSphere karlssonOEISQ2.center karlssonOEISQ2.radius := by
  apply euclideanSphere_ne_of_radius_ne
  norm_num [karlssonOEISQ1, karlssonOEISQ2,
    EuclideanLollipop.fromCenter, EuclideanLollipop.fromAnchor]

/-- The OEIS `Q1` and `Q3` lifted circles are different, already because
their radii are different. -/
theorem karlssonOEISQ1_Q3_spheres_distinct :
    euclideanSphere karlssonOEISQ1.center karlssonOEISQ1.radius ≠
      euclideanSphere karlssonOEISQ3.center karlssonOEISQ3.radius := by
  apply euclideanSphere_ne_of_radius_ne
  norm_num [karlssonOEISQ1, karlssonOEISQ3,
    EuclideanLollipop.fromCenter, EuclideanLollipop.fromAnchor]

/-- The `y`-coordinate of the OEIS `Q2` circle center is positive. -/
theorem karlssonOEISQ2_center_y_pos :
    0 < karlssonOEISQ2.center 1 := by
  have hcos : 0 < Real.cos (2 * Real.pi / 15) := by
    apply Real.cos_pos_of_mem_Ioo
    constructor <;> nlinarith [Real.pi_pos]
  have hsin :
      Real.sin karlssonOEISQ2Theta =
        -Real.cos (2 * Real.pi / 15) := by
    rw [karlssonOEISQ2Theta, Real.sin_neg]
    rw [show Real.pi / 2 + 2 * Real.pi / 15 =
      2 * Real.pi / 15 + Real.pi / 2 by ring]
    rw [Real.sin_add_pi_div_two]
  simp [karlssonOEISQ2, EuclideanLollipop.fromAnchor,
    angleDirection, point2, hsin]
  nlinarith

/-- The `y`-coordinate of the OEIS `Q3` circle center is negative. -/
theorem karlssonOEISQ3_center_y_neg :
    karlssonOEISQ3.center 1 < 0 := by
  have hcos : 0 < Real.cos (Real.pi / 30) := by
    apply Real.cos_pos_of_mem_Ioo
    constructor <;> nlinarith [Real.pi_pos]
  have hsin :
      Real.sin karlssonOEISQ3Theta =
        Real.cos (Real.pi / 30) := by
    rw [karlssonOEISQ3Theta]
    rw [show Real.pi / 2 + Real.pi / 30 =
      Real.pi / 30 + Real.pi / 2 by ring]
    rw [Real.sin_add_pi_div_two]
  simp [karlssonOEISQ3, EuclideanLollipop.fromAnchor,
    angleDirection, point2, hsin]
  nlinarith

/-- The OEIS `Q2` and `Q3` lifted circles are different.  They have the same
radius, so this proof uses the signs of their center `y`-coordinates. -/
theorem karlssonOEISQ2_Q3_spheres_distinct :
    euclideanSphere karlssonOEISQ2.center karlssonOEISQ2.radius ≠
      euclideanSphere karlssonOEISQ3.center karlssonOEISQ3.radius := by
  apply euclideanSphere_ne_of_center_ne
  intro hcenter
  have hy : karlssonOEISQ2.center 1 = karlssonOEISQ3.center 1 :=
    congr_fun hcenter 1
  have hq3_pos : 0 < karlssonOEISQ3.center 1 := by
    simpa [hy] using karlssonOEISQ2_center_y_pos
  exact (not_lt_of_ge hq3_pos.le) karlssonOEISQ3_center_y_neg

/-- The OEIS `Q0` and `Q1` ray-supporting lines are different. -/
theorem karlssonOEISQ0_Q1_rayLines_distinct :
    euclideanRayLine karlssonOEISQ0 ≠ euclideanRayLine karlssonOEISQ1 := by
  apply euclideanRayLine_ne_of_det2_rayDirection_ne_zero
  have hsin_pos : 0 < Real.sin ((1 : ℝ) / 100) := by
    apply Real.sin_pos_of_pos_of_lt_pi
    · norm_num
    · nlinarith [Real.pi_gt_three]
  have hdet :
      det2 karlssonOEISQ0.rayDirection karlssonOEISQ1.rayDirection =
        -Real.sin ((1 : ℝ) / 100) := by
    simp [karlssonOEISQ0, karlssonOEISQ1,
      EuclideanLollipop.fromAnchor, EuclideanLollipop.fromCenter,
      angleDirection, det2, point2, Real.sin_neg]
  rw [hdet]
  exact neg_ne_zero.mpr hsin_pos.ne'

/-- In the exceptional OEIS base pair, the `Q1` ray anchor is strictly
outside the `Q0` circle. -/
theorem karlssonOEISQ0_Q1_circleRay_anchor_distSq_gt_radius_sq :
    karlssonOEISQ0.radius ^ 2 <
      distSq2 karlssonOEISQ1.anchor karlssonOEISQ0.center := by
  have hcos_pos : 0 < Real.cos ((1 / 100 : ℝ)) := by
    apply Real.cos_pos_of_mem_Ioo
    constructor <;> nlinarith [Real.pi_gt_three]
  let x : ℝ := 200 + 45 / 100 + 55 / 100 * Real.cos ((1 / 100 : ℝ))
  let y : ℝ := 4 / 10 - 55 / 100 * Real.sin ((1 / 100 : ℝ))
  have hx_gt : (200 : ℝ) < x := by
    dsimp [x]
    nlinarith
  have hx_sq_gt : (200 : ℝ) ^ 2 < x ^ 2 :=
    (sq_lt_sq₀ (by norm_num) (by nlinarith)).2 hx_gt
  have hy_sq_nonneg : 0 ≤ y ^ 2 := sq_nonneg y
  dsimp [x, y] at hx_sq_gt hy_sq_nonneg
  unfold distSq2 normSq2 dot2
  simp [karlssonOEISQ0, karlssonOEISQ1,
    EuclideanLollipop.fromAnchor, EuclideanLollipop.fromCenter,
    angleDirection, point2, Real.cos_neg, Real.sin_neg]
  nlinarith

/-- In the exceptional OEIS base pair, the `Q1` ray points weakly away from
the `Q0` center. -/
theorem karlssonOEISQ0_Q1_circleRay_anchor_dot_nonneg :
    0 ≤
      dot2 (karlssonOEISQ1.anchor - karlssonOEISQ0.center)
        karlssonOEISQ1.rayDirection := by
  have hcos_pos : 0 < Real.cos ((1 / 100 : ℝ)) := by
    apply Real.cos_pos_of_mem_Ioo
    constructor <;> nlinarith [Real.pi_gt_three]
  have hsin_le_one : Real.sin ((1 / 100 : ℝ)) ≤ 1 :=
    Real.sin_le_one ((1 / 100 : ℝ))
  have htrig := Real.cos_sq_add_sin_sq ((1 / 100 : ℝ))
  unfold dot2
  simp [karlssonOEISQ0, karlssonOEISQ1,
    EuclideanLollipop.fromAnchor, EuclideanLollipop.fromCenter,
    angleDirection, point2, Real.cos_neg, Real.sin_neg]
  nlinarith

/-- Therefore the `circle(Q0) ∩ ray(Q1)` component is empty. -/
theorem karlssonOEISQ0_Q1_circleRaySet_empty :
    ∀ p : EuclideanR2,
      p ∉ euclideanCircleRaySet karlssonOEISQ0 karlssonOEISQ1 :=
  euclideanCircleRaySet_empty_of_radius_sq_lt_anchor_distSq2_of_dot_nonneg
    karlssonOEISQ0_Q1_circleRay_anchor_distSq_gt_radius_sq
    karlssonOEISQ0_Q1_circleRay_anchor_dot_nonneg

/-- For the exceptional OEIS base pair, the `Q1` ray starts outside the `Q0`
circle and points weakly away from the `Q0` center.  Hence the
circle-ray component `circle(Q0) ∩ ray(Q1)` is empty, giving a concrete
named `<= 5` savings route for the close pair. -/
noncomputable def karlssonOEISQ0_Q1_circleRayOutward_savings_route :
    PairComponentSavingsFiveRoute karlssonOEISQ0 karlssonOEISQ1 :=
  PairComponentSavingsFiveRoute.circleRayOutward
    karlssonOEISQ0_Q1_spheres_distinct
    karlssonOEISQ0_Q1_rayLines_distinct
    karlssonOEISQ0_Q1_circleRay_anchor_distSq_gt_radius_sq
    karlssonOEISQ0_Q1_circleRay_anchor_dot_nonneg

/-- The OEIS `Q0` and `Q2` ray-supporting lines are different. -/
theorem karlssonOEISQ0_Q2_rayLines_distinct :
    euclideanRayLine karlssonOEISQ0 ≠ euclideanRayLine karlssonOEISQ2 := by
  apply euclideanRayLine_ne_of_det2_rayDirection_ne_zero
  have hsin_pos : 0 < Real.sin (Real.pi / 2 + 2 * Real.pi / 15) := by
    apply Real.sin_pos_of_pos_of_lt_pi
    · nlinarith [Real.pi_pos]
    · nlinarith [Real.pi_pos]
  intro hzero
  have hzero' :
      Real.sin (-(2 * Real.pi / 15) + -(Real.pi / 2)) = 0 := by
    simpa [karlssonOEISQ0, karlssonOEISQ2,
      EuclideanLollipop.fromAnchor, angleDirection, det2, point2,
      karlssonOEISQ2Theta] using hzero
  have hangle :
      -(2 * Real.pi / 15) + -(Real.pi / 2) =
        -(Real.pi / 2 + 2 * Real.pi / 15) := by
    ring
  rw [hangle, Real.sin_neg] at hzero'
  exact hsin_pos.ne' (neg_eq_zero.mp hzero')

/-- The OEIS `Q0` and `Q3` ray-supporting lines are different. -/
theorem karlssonOEISQ0_Q3_rayLines_distinct :
    euclideanRayLine karlssonOEISQ0 ≠ euclideanRayLine karlssonOEISQ3 := by
  apply euclideanRayLine_ne_of_det2_rayDirection_ne_zero
  have hsin_pos : 0 < Real.sin (Real.pi / 2 + Real.pi / 30) := by
    apply Real.sin_pos_of_pos_of_lt_pi
    · nlinarith [Real.pi_pos]
    · nlinarith [Real.pi_pos]
  have hdet :
      det2 karlssonOEISQ0.rayDirection karlssonOEISQ3.rayDirection =
        Real.sin (Real.pi / 2 + Real.pi / 30) := by
    simp [karlssonOEISQ0, karlssonOEISQ3,
      EuclideanLollipop.fromAnchor, angleDirection, det2, point2,
      karlssonOEISQ3Theta]
  rw [hdet]
  exact hsin_pos.ne'

/-- The OEIS `Q1` and `Q2` ray-supporting lines are different. -/
theorem karlssonOEISQ1_Q2_rayLines_distinct :
    euclideanRayLine karlssonOEISQ1 ≠ euclideanRayLine karlssonOEISQ2 := by
  apply euclideanRayLine_ne_of_det2_rayDirection_ne_zero
  intro hzero
  let x : ℝ := (1 : ℝ) / 100 - (Real.pi / 2 + 2 * Real.pi / 15)
  have hsin_neg : Real.sin x < 0 := by
    apply Real.sin_neg_of_neg_of_neg_pi_lt
    · dsimp [x]
      nlinarith [Real.pi_gt_three]
    · dsimp [x]
      nlinarith [Real.pi_pos]
  have hzero' : Real.sin x = 0 := by
    have hraw :
        Real.sin (karlssonOEISQ2Theta - (-(1 / 100 : ℝ))) = 0 := by
      simpa [karlssonOEISQ1, karlssonOEISQ2,
        EuclideanLollipop.fromCenter, EuclideanLollipop.fromAnchor,
        det2_angleDirection] using hzero
    have hangle :
        karlssonOEISQ2Theta - (-(1 / 100 : ℝ)) = x := by
      dsimp [x, karlssonOEISQ2Theta]
      ring
    rwa [hangle] at hraw
  exact hsin_neg.ne hzero'

/-- The OEIS `Q1` and `Q3` ray-supporting lines are different. -/
theorem karlssonOEISQ1_Q3_rayLines_distinct :
    euclideanRayLine karlssonOEISQ1 ≠ euclideanRayLine karlssonOEISQ3 := by
  apply euclideanRayLine_ne_of_det2_rayDirection_ne_zero
  let x : ℝ := Real.pi / 2 + Real.pi / 30 + (1 : ℝ) / 100
  have hsin_pos : 0 < Real.sin x := by
    apply Real.sin_pos_of_pos_of_lt_pi
    · dsimp [x]
      nlinarith [Real.pi_pos]
    · dsimp [x]
      nlinarith [Real.pi_gt_three]
  intro hzero
  have hzero' : Real.sin x = 0 := by
    have hraw :
        Real.sin (karlssonOEISQ3Theta - (-(1 / 100 : ℝ))) = 0 := by
      simpa [karlssonOEISQ1, karlssonOEISQ3,
        EuclideanLollipop.fromCenter, EuclideanLollipop.fromAnchor,
        det2_angleDirection] using hzero
    have hangle :
        karlssonOEISQ3Theta - (-(1 / 100 : ℝ)) = x := by
      dsimp [x, karlssonOEISQ3Theta]
      ring
    rwa [hangle] at hraw
  exact hsin_pos.ne' hzero'

/-- The OEIS `Q2` and `Q3` ray-supporting lines are different. -/
theorem karlssonOEISQ2_Q3_rayLines_distinct :
    euclideanRayLine karlssonOEISQ2 ≠ euclideanRayLine karlssonOEISQ3 := by
  apply euclideanRayLine_ne_of_det2_rayDirection_ne_zero
  intro hzero
  have hsin_pos : 0 < Real.sin (Real.pi / 6) := by
    apply Real.sin_pos_of_pos_of_lt_pi
    · nlinarith [Real.pi_pos]
    · nlinarith [Real.pi_pos]
  have hzero' : -Real.sin (Real.pi / 6) = 0 := by
    have hraw :
        Real.sin (karlssonOEISQ3Theta - karlssonOEISQ2Theta) = 0 := by
      simpa [karlssonOEISQ2, karlssonOEISQ3,
        EuclideanLollipop.fromAnchor, det2_angleDirection] using hzero
    have hangle :
        karlssonOEISQ3Theta - karlssonOEISQ2Theta =
          Real.pi / 6 + Real.pi := by
      dsimp [karlssonOEISQ2Theta, karlssonOEISQ3Theta]
      ring
    rw [hangle, Real.sin_add_pi] at hraw
    exact hraw
  exact hsin_pos.ne' (neg_eq_zero.mp hzero')

/-- Uniform lifted-circle noncoincidence theorem for all six unordered pairs
of the OEIS/Karlsson base arrangement. -/
theorem karlssonOEISBase_spheres_distinct
    {i j : Fin 4} (hij : i < j) :
    euclideanSphere (karlssonOEISBaseArrangement.lollipop i).center
        (karlssonOEISBaseArrangement.lollipop i).radius ≠
      euclideanSphere (karlssonOEISBaseArrangement.lollipop j).center
        (karlssonOEISBaseArrangement.lollipop j).radius := by
  fin_cases i <;> fin_cases j <;> simp at hij ⊢ <;>
    first
    | exact karlssonOEISQ0_Q1_spheres_distinct
    | exact karlssonOEISQ0_Q2_spheres_distinct
    | exact karlssonOEISQ0_Q3_spheres_distinct
    | exact karlssonOEISQ1_Q2_spheres_distinct
    | exact karlssonOEISQ1_Q3_spheres_distinct
    | exact karlssonOEISQ2_Q3_spheres_distinct

/-- Uniform ray-supporting-line noncoincidence theorem for all six unordered
pairs of the OEIS/Karlsson base arrangement. -/
theorem karlssonOEISBase_rayLines_distinct
    {i j : Fin 4} (hij : i < j) :
    euclideanRayLine (karlssonOEISBaseArrangement.lollipop i) ≠
      euclideanRayLine (karlssonOEISBaseArrangement.lollipop j) := by
  fin_cases i <;> fin_cases j <;> simp at hij ⊢ <;>
    first
    | exact karlssonOEISQ0_Q1_rayLines_distinct
    | exact karlssonOEISQ0_Q2_rayLines_distinct
    | exact karlssonOEISQ0_Q3_rayLines_distinct
    | exact karlssonOEISQ1_Q2_rayLines_distinct
    | exact karlssonOEISQ1_Q3_rayLines_distinct
    | exact karlssonOEISQ2_Q3_rayLines_distinct

/-- Once the exact OEIS/Karlsson base carrier-intersection certificate is
supplied, the generic component-count theorem recovers the universal
`<= 7` crossing bound for every base pair from the checked noncoincidence
facts above. -/
theorem KarlssonOEISBaseCoordinateCrossingCertificate.cross_le_seven
    (C : KarlssonOEISBaseCoordinateCrossingCertificate)
    {i j : Fin 4} (hij : i < j) :
    karlssonBasePairCrossing i j ≤ 7 :=
  pairwiseCarrierCrossingData_cross_le_seven
    C.pairwise_crossings hij
    (karlssonOEISBase_spheres_distinct hij)
    (karlssonOEISBase_rayLines_distinct hij)

/-- Six independent pair certificates imply the generic `<= 7` crossing bound
for every exact OEIS/Karlsson base pair after assembly. -/
theorem KarlssonOEISBaseSixPairCoordinateCrossingCertificate.cross_le_seven
    (C : KarlssonOEISBaseSixPairCoordinateCrossingCertificate)
    {i j : Fin 4} (hij : i < j) :
    karlssonBasePairCrossing i j ≤ 7 :=
  C.toCoordinateCrossingCertificate.cross_le_seven hij

/-- The exact OEIS `(Q0,Q1)` pair forms a complete primitive routed local
pair-data object once the six-pair local finite carrier witness is supplied.
The close branch uses the concrete half-line-outward route; the intriguing
branches are impossible because the pair is not intriguing. -/
noncomputable def KarlssonOEISBaseSixPairCoordinateCrossingCertificate.zero_one_primitiveRoutedLocalPairData
    (C : KarlssonOEISBaseSixPairCoordinateCrossingCertificate) :
    PrimitiveRoutedLocalPairData
      karlssonOEISBaseArrangement karlssonBasePairCrossing
      (0 : Fin 4) (1 : Fin 4) (by decide) where
  carrier_crossing :=
    C.localPairCarrierCrossingData (0 : Fin 4) (1 : Fin 4) (by decide)
  spheres_distinct := by
    simpa using karlssonOEISQ0_Q1_spheres_distinct
  rayLines_distinct := by
    simpa using karlssonOEISQ0_Q1_rayLines_distinct
  close_savings_route := by
    intro _hclose
    simpa using karlssonOEISQ0_Q1_circleRayOutward_savings_route
  intriguing_savings_route := by
    intro hintriguing
    exact False.elim (karlssonOEISBase_zero_one_not_circleIntriguing hintriguing)
  close_intriguing_savings_route := by
    intro _hclose hintriguing
    exact False.elim (karlssonOEISBase_zero_one_not_circleIntriguing hintriguing)

/-- For the exceptional OEIS base pair `(Q0,Q1)`, the concrete
circle-ray-outward route and the local finite pair certificate already prove
the sharp `<= 5` crossing bound. -/
theorem KarlssonOEISBaseSixPairCoordinateCrossingCertificate.zero_one_cross_le_five
    (C : KarlssonOEISBaseSixPairCoordinateCrossingCertificate) :
    karlssonBasePairCrossing (0 : Fin 4) (1 : Fin 4) ≤ 5 := by
  have h :=
    localPairCarrierCrossingData_cross_le_of_pairComponentSavings
      (C.localPairCarrierCrossingData (0 : Fin 4) (1 : Fin 4) (by decide))
      karlssonOEISQ0_Q1_circleRayOutward_savings_route.toPairComponentSavings
  exact h

/-- Cardinality form of the concrete `(Q0,Q1)` route: the finite witness set
for the exceptional OEIS base pair has at most five points. -/
theorem KarlssonOEISBaseSixPairCoordinateCrossingCertificate.zero_one_card_le_five
    (C : KarlssonOEISBaseSixPairCoordinateCrossingCertificate) :
    C.pair01.crossingPoints.card ≤ 5 := by
  have h :=
    localPairCarrierCrossingData_lifted_card_le_of_pairComponentSavings
      (C.localPairCarrierCrossingData (0 : Fin 4) (1 : Fin 4) (by decide))
      karlssonOEISQ0_Q1_circleRayOutward_savings_route.toPairComponentSavings
  simpa [KarlssonOEISBaseSixPairCoordinateCrossingCertificate.crossingPoints,
    KarlssonOEISBaseSixPairCoordinateCrossingCertificate.localPairCarrierCrossingData]
    using h

/-- Cardinality form of the same generic `<= 7` bound for the finite
carrier-intersection witnesses in the exact OEIS/Karlsson base certificate. -/
theorem KarlssonOEISBaseCoordinateCrossingCertificate.crossingPoints_card_le_seven
    (C : KarlssonOEISBaseCoordinateCrossingCertificate)
    {i j : Fin 4} (hij : i < j) :
    (C.pairwise_crossings.crossingPoints i j hij).card ≤ 7 := by
  have hcard_rat :
      (((C.pairwise_crossings.crossingPoints i j hij).card : Nat) : Rat) ≤
        (7 : Rat) := by
    rw [C.crossingPoints_card_eq_base hij]
    exact C.cross_le_seven hij
  exact_mod_cast hcard_rat

end ExplicitInputs
end TheoremOneManuscript
end Lollipop
