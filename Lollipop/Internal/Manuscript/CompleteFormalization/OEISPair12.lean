import Lollipop.Internal.Manuscript.CompleteFormalization.OEISSevenPoint
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.Analysis.Real.Sqrt
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds

/-!
Concrete component witnesses for the OEIS/Karlsson base pair `(Q1,Q2)`.

This file starts the exact `= 7` work for `(Q1,Q2)` by proving the ray-ray
component point.  The `Q1` ray has tiny bearing `-1/100`, so the forward-time
positivity proof uses explicit trigonometric bounds rather than decimal
approximations.
-/

namespace Lollipop
namespace TheoremOneManuscript
namespace CompleteFormalization

open PrimitiveGeometry

namespace OEISPair12

noncomputable section

open ExplicitInputs
open TheoremOneEndToEnd.PaulsenLinearAlgebra (distSq2 normSq2 dot2)

private abbrev theta : ℝ := (1 : ℝ) / 100
private abbrev alpha : ℝ := 2 * Real.pi / 15

private theorem theta_pos : 0 < theta := by
  norm_num [theta]

private theorem theta_lt_pi : theta < Real.pi := by
  have htheta : theta < (3 : ℝ) := by
    norm_num [theta]
  exact htheta.trans Real.pi_gt_three

private theorem alpha_pos : 0 < alpha := by
  dsimp [alpha]
  nlinarith [Real.pi_pos]

private theorem alpha_lt_pi_div_two : alpha < Real.pi / 2 := by
  dsimp [alpha]
  nlinarith [Real.pi_pos]

private theorem sin_theta_pos : 0 < Real.sin theta :=
  Real.sin_pos_of_pos_of_lt_pi theta_pos theta_lt_pi

private theorem sin_theta_lt_theta : Real.sin theta < theta :=
  Real.sin_lt theta_pos

private theorem cos_theta_pos : 0 < Real.cos theta := by
  apply Real.cos_pos_of_mem_Ioo
  constructor <;> nlinarith [theta_pos, Real.pi_gt_three]

private theorem cos_theta_gt_one_half :
    (1 : ℝ) / 2 < Real.cos theta := by
  have hcos :=
    Real.one_sub_sq_div_two_lt_cos
      (x := theta) theta_pos.ne'
  have hhalf : (1 : ℝ) / 2 < 1 - theta ^ 2 / 2 := by
    norm_num [theta]
  exact hhalf.trans hcos

private theorem sin_alpha_pos : 0 < Real.sin alpha := by
  apply Real.sin_pos_of_pos_of_lt_pi
  · exact alpha_pos
  · nlinarith [alpha_lt_pi_div_two, Real.pi_pos]

private theorem cos_alpha_pos : 0 < Real.cos alpha := by
  apply Real.cos_pos_of_mem_Ioo
  constructor
  · nlinarith [alpha_pos, Real.pi_pos]
  · exact alpha_lt_pi_div_two

private theorem alpha_sq_lt_nine_div_fifty :
    alpha ^ 2 < (9 : ℝ) / 50 := by
  have halpha_lt : alpha < (42 : ℝ) / 100 := by
    dsimp [alpha]
    nlinarith [Real.pi_lt_d2]
  nlinarith [alpha_pos, halpha_lt]

private theorem cos_alpha_gt_ninety_one_div_hundred :
    (91 : ℝ) / 100 < Real.cos alpha := by
  have hcos :=
    Real.one_sub_sq_div_two_lt_cos
      (x := alpha) alpha_pos.ne'
  have hbase : (91 : ℝ) / 100 < 1 - alpha ^ 2 / 2 := by
    nlinarith [alpha_sq_lt_nine_div_fifty]
  exact hbase.trans hcos

private theorem sin_alpha_lt_twenty_one_div_fifty :
    Real.sin alpha < (21 : ℝ) / 50 := by
  have htrig := Real.sin_sq_add_cos_sq alpha
  have hsq :
      Real.sin alpha ^ 2 < ((21 : ℝ) / 50) ^ 2 := by
    nlinarith [htrig, cos_alpha_gt_ninety_one_div_hundred]
  exact
    (sq_lt_sq₀ sin_alpha_pos.le
      (by norm_num : (0 : ℝ) ≤ (21 : ℝ) / 50)).1 hsq

private theorem alpha_lt_one : alpha ≤ 1 := by
  dsimp [alpha]
  nlinarith [Real.pi_lt_d2]

private theorem sin_alpha_gt_two_div_five :
    (2 : ℝ) / 5 < Real.sin alpha := by
  have hsin := Real.sin_gt_sub_cube alpha_pos alpha_lt_one
  have hbase : (2 : ℝ) / 5 < alpha - alpha ^ 3 / 4 := by
    have halpha_gt : (157 : ℝ) / 375 < alpha := by
      dsimp [alpha]
      nlinarith [Real.pi_gt_d2]
    have halpha_lt : alpha < (21 : ℝ) / 50 := by
      dsimp [alpha]
      nlinarith [Real.pi_lt_d2]
    have hcube : alpha ^ 3 < ((21 : ℝ) / 50) ^ 3 :=
      pow_lt_pow_left₀ halpha_lt alpha_pos.le (by norm_num)
    have hnum :
        (2 : ℝ) / 5 <
          (157 : ℝ) / 375 - (((21 : ℝ) / 50) ^ 3) / 4 := by
      norm_num
    nlinarith
  exact hbase.trans hsin

theorem q2_theta_sin :
    Real.sin karlssonOEISQ2Theta = -Real.cos alpha := by
  rw [karlssonOEISQ2Theta, Real.sin_neg]
  rw [show Real.pi / 2 + 2 * Real.pi / 15 =
    alpha + Real.pi / 2 by
      dsimp [alpha]
      ring]
  rw [Real.sin_add_pi_div_two]

theorem q2_theta_cos :
    Real.cos karlssonOEISQ2Theta = -Real.sin alpha := by
  rw [karlssonOEISQ2Theta, Real.cos_neg]
  rw [show Real.pi / 2 + 2 * Real.pi / 15 =
    alpha + Real.pi / 2 by
      dsimp [alpha]
      ring]
  rw [Real.cos_add_pi_div_two]

private abbrev q1q2AnchorX : ℝ :=
  (45 : ℝ) / 100 + ((55 : ℝ) / 100) * Real.cos theta

private abbrev q1q2AnchorY : ℝ :=
  (4 : ℝ) / 10 - ((55 : ℝ) / 100) * Real.sin theta

private abbrev q1q2DeltaX : ℝ :=
  (23 : ℝ) / 20 - q1q2AnchorX

private abbrev q1q2DeltaY : ℝ :=
  (13 : ℝ) / 20 - q1q2AnchorY

private abbrev q1q2Denom : ℝ :=
  Real.cos theta * Real.cos alpha +
    Real.sin theta * Real.sin alpha

private theorem q1_anchor_eq :
    karlssonOEISQ1.anchor =
      point2 q1q2AnchorX q1q2AnchorY := by
  ext i
  fin_cases i
  · simp [karlssonOEISQ1, EuclideanLollipop.fromCenter, angleDirection,
      point2, q1q2AnchorX, theta, Real.cos_neg,
      Real.sin_neg]
  · simp [karlssonOEISQ1, EuclideanLollipop.fromCenter, angleDirection,
      point2, q1q2AnchorY, theta, Real.cos_neg,
      Real.sin_neg]
    ring

private theorem q1q2Denom_pos : 0 < q1q2Denom := by
  unfold q1q2Denom
  have hmain :
      0 < Real.cos theta * Real.cos alpha :=
    mul_pos cos_theta_pos cos_alpha_pos
  have htail :
      0 < Real.sin theta * Real.sin alpha :=
    mul_pos sin_theta_pos sin_alpha_pos
  nlinarith

private theorem q1q2DeltaX_ge_three_div_twenty :
    (3 : ℝ) / 20 ≤ q1q2DeltaX := by
  unfold q1q2DeltaX q1q2AnchorX
  have hcos_le : Real.cos theta ≤ 1 := Real.cos_le_one theta
  nlinarith

private theorem q1q2DeltaX_pos : 0 < q1q2DeltaX := by
  nlinarith [q1q2DeltaX_ge_three_div_twenty]

private theorem q1q2DeltaX_lt_one :
    q1q2DeltaX < 1 := by
  unfold q1q2DeltaX q1q2AnchorX
  nlinarith [cos_theta_pos]

private theorem q1q2DeltaY_pos : 0 < q1q2DeltaY := by
  unfold q1q2DeltaY q1q2AnchorY
  nlinarith [sin_theta_pos]

private theorem q1q2DeltaY_lt_five_eleven_div_two_thousand :
    q1q2DeltaY < (511 : ℝ) / 2000 := by
  unfold q1q2DeltaY q1q2AnchorY
  have hsmall : Real.sin theta < (1 : ℝ) / 100 := by
    simpa [theta] using sin_theta_lt_theta
  nlinarith [hsmall]

private theorem q1q2DeltaY_lt_one :
    q1q2DeltaY < 1 := by
  nlinarith [q1q2DeltaY_lt_five_eleven_div_two_thousand]

private theorem q1q2_timeQ1_numerator_pos :
    0 < q1q2DeltaX * Real.cos alpha -
      q1q2DeltaY * Real.sin alpha := by
  have hleft :
      ((3 : ℝ) / 20) * ((91 : ℝ) / 100) <
        q1q2DeltaX * Real.cos alpha := by
    nlinarith [q1q2DeltaX_ge_three_div_twenty,
      q1q2DeltaX_pos, cos_alpha_gt_ninety_one_div_hundred]
  have hright :
      q1q2DeltaY * Real.sin alpha <
        ((511 : ℝ) / 2000) * ((21 : ℝ) / 50) := by
    nlinarith [q1q2DeltaY_lt_five_eleven_div_two_thousand,
      q1q2DeltaY_pos, sin_alpha_lt_twenty_one_div_fifty,
      sin_alpha_pos]
  nlinarith [hleft, hright]

private theorem q1q2_timeQ2_numerator_pos :
    0 < q1q2DeltaX * Real.sin theta +
      q1q2DeltaY * Real.cos theta := by
  have hx :
      0 < q1q2DeltaX * Real.sin theta :=
    mul_pos q1q2DeltaX_pos sin_theta_pos
  have hy :
      0 < q1q2DeltaY * Real.cos theta :=
    mul_pos q1q2DeltaY_pos cos_theta_pos
  nlinarith

/-- Forward time along the `Q1` ray to the `(Q1,Q2)` ray-ray point. -/
noncomputable def q1q2RayRayTimeQ1 : ℝ :=
  (q1q2DeltaX * Real.cos alpha -
    q1q2DeltaY * Real.sin alpha) / q1q2Denom

/-- Forward time along the `Q2` ray to the same point. -/
noncomputable def q1q2RayRayTimeQ2 : ℝ :=
  (q1q2DeltaX * Real.sin theta +
    q1q2DeltaY * Real.cos theta) / q1q2Denom

/-- The concrete ray-ray point for the OEIS/Karlsson pair `(Q1,Q2)`. -/
noncomputable def q1q2RayRayPoint : R2 :=
  karlssonOEISQ1.anchor + q1q2RayRayTimeQ1 • karlssonOEISQ1.rayDirection

theorem q1q2RayRayTimeQ1_pos : 0 < q1q2RayRayTimeQ1 := by
  unfold q1q2RayRayTimeQ1
  exact div_pos q1q2_timeQ1_numerator_pos q1q2Denom_pos

theorem q1q2RayRayTimeQ2_pos : 0 < q1q2RayRayTimeQ2 := by
  unfold q1q2RayRayTimeQ2
  exact div_pos q1q2_timeQ2_numerator_pos q1q2Denom_pos

/-- The `Q1`-ray expression for the ray-ray point equals the `Q2`-ray
expression. -/
theorem q1q2RayRayPoint_eq_q2_ray_expression :
    q1q2RayRayPoint =
      karlssonOEISQ2.anchor +
        q1q2RayRayTimeQ2 • karlssonOEISQ2.rayDirection := by
  have hden_ne : q1q2Denom ≠ 0 := q1q2Denom_pos.ne'
  ext i
  fin_cases i
  · unfold q1q2RayRayPoint q1q2RayRayTimeQ1 q1q2RayRayTimeQ2
      q1q2DeltaX q1q2DeltaY q1q2AnchorX q1q2AnchorY q1q2Denom
    simp [karlssonOEISQ1, karlssonOEISQ2, EuclideanLollipop.fromCenter,
      EuclideanLollipop.fromAnchor, angleDirection, point2, theta,
      Real.cos_neg, Real.sin_neg, q2_theta_cos, q2_theta_sin]
    field_simp [hden_ne]
    ring
  · unfold q1q2RayRayPoint q1q2RayRayTimeQ1 q1q2RayRayTimeQ2
      q1q2DeltaX q1q2DeltaY q1q2AnchorX q1q2AnchorY q1q2Denom
    simp [karlssonOEISQ1, karlssonOEISQ2, EuclideanLollipop.fromCenter,
      EuclideanLollipop.fromAnchor, angleDirection, point2, theta,
      Real.cos_neg, Real.sin_neg, q2_theta_cos, q2_theta_sin]
    field_simp [hden_ne]
    ring

theorem q1q2RayRayPoint_mem_q1_ray :
    q1q2RayRayPoint ∈
      raySet karlssonOEISQ1.anchor karlssonOEISQ1.rayDirection := by
  exact ⟨q1q2RayRayTimeQ1, q1q2RayRayTimeQ1_pos.le, rfl⟩

theorem q1q2RayRayPoint_mem_q2_ray :
    q1q2RayRayPoint ∈
      raySet karlssonOEISQ2.anchor karlssonOEISQ2.rayDirection := by
  exact ⟨q1q2RayRayTimeQ2, q1q2RayRayTimeQ2_pos.le,
    q1q2RayRayPoint_eq_q2_ray_expression⟩

/-- Lifted ray-ray component form of the concrete `(Q1,Q2)` ray-ray point. -/
theorem q1q2RayRayPoint_mem_euclideanRayRaySet :
    toEuclideanR2 q1q2RayRayPoint ∈
      euclideanRayRaySet karlssonOEISQ1 karlssonOEISQ2 :=
  mem_euclideanRayRaySet_of_mem_raySets
    q1q2RayRayPoint_mem_q1_ray q1q2RayRayPoint_mem_q2_ray

/-- Arrangement-indexed primitive carrier-intersection form. -/
theorem q1q2RayRayPoint_mem_base_pairIntersectionSet :
    q1q2RayRayPoint ∈
      karlssonOEISBaseArrangement.pairIntersectionSet
        (1 : Fin 4) (2 : Fin 4) := by
  exact
    OEISSevenPoint.pair_mem_of_euclideanRayRay
      (i := (1 : Fin 4)) (j := (2 : Fin 4))
      (p := q1q2RayRayPoint)
      (by
        simpa [karlssonOEISBaseArrangement] using
          q1q2RayRayPoint_mem_euclideanRayRaySet)

private theorem ray_point_mem_circle_of_quadratic
    {anchor center direction : R2} {radius dot constant t : ℝ}
    (hdot : dot = -dot2 (anchor - center) direction)
    (hconstant : constant = distSq2 anchor center - radius ^ 2)
    (hnorm : normSq2 direction = 1)
    (hquad : t ^ 2 - 2 * dot * t + constant = 0) :
    anchor + t • direction ∈ circleSet center radius := by
  unfold circleSet
  change distSq2 (anchor + t • direction) center = radius ^ 2
  rw [distSq2_vadd_smul_sub]
  rw [hnorm]
  rw [hconstant] at hquad
  rw [hdot] at hquad
  nlinarith

private theorem q1_rayDirection_normSq :
    normSq2 karlssonOEISQ1.rayDirection = 1 := by
  simpa [karlssonOEISQ1, EuclideanLollipop.fromCenter] using
    normSq2_angleDirection (-(100 : ℝ)⁻¹)

private theorem q2_rayDirection_normSq :
    normSq2 karlssonOEISQ2.rayDirection = 1 := by
  simpa [karlssonOEISQ2, EuclideanLollipop.fromAnchor] using
    normSq2_angleDirection karlssonOEISQ2Theta

/-- Positive dot coefficient in the quadratic for
`circle(Q1) ∩ ray(Q2)`. -/
private abbrev q1q2CircleRayDot : ℝ :=
  -dot2 (karlssonOEISQ2.anchor - karlssonOEISQ1.center)
    karlssonOEISQ2.rayDirection

/-- Constant term in the quadratic for `circle(Q1) ∩ ray(Q2)`. -/
private abbrev q1q2CircleRayConstant : ℝ :=
  distSq2 karlssonOEISQ2.anchor karlssonOEISQ1.center -
    karlssonOEISQ1.radius ^ 2

/-- Discriminant for `circle(Q1) ∩ ray(Q2)`. -/
private abbrev q1q2CircleRayDiscriminant : ℝ :=
  q1q2CircleRayDot ^ 2 - q1q2CircleRayConstant

private theorem q1q2CircleRayDot_expanded :
    q1q2CircleRayDot =
      ((7 : ℝ) / 10) * Real.sin alpha +
        ((1 : ℝ) / 4) * Real.cos alpha := by
  unfold q1q2CircleRayDot dot2
  simp [karlssonOEISQ1, karlssonOEISQ2, EuclideanLollipop.fromCenter,
    EuclideanLollipop.fromAnchor, angleDirection, point2,
    q2_theta_cos, q2_theta_sin]
  ring

private theorem q1q2CircleRayConstant_expanded :
    q1q2CircleRayConstant = (1 : ℝ) / 4 := by
  unfold q1q2CircleRayConstant distSq2 normSq2 dot2
  simp [karlssonOEISQ1, karlssonOEISQ2, EuclideanLollipop.fromCenter,
    EuclideanLollipop.fromAnchor, angleDirection, point2]
  norm_num

private theorem q1q2CircleRayDot_gt_one_half :
    (1 : ℝ) / 2 < q1q2CircleRayDot := by
  rw [q1q2CircleRayDot_expanded]
  nlinarith [sin_alpha_gt_two_div_five,
    cos_alpha_gt_ninety_one_div_hundred]

private theorem q1q2CircleRayDot_pos :
    0 < q1q2CircleRayDot := by
  nlinarith [q1q2CircleRayDot_gt_one_half]

private theorem q1q2CircleRayConstant_pos :
    0 < q1q2CircleRayConstant := by
  rw [q1q2CircleRayConstant_expanded]
  norm_num

private theorem q1q2CircleRayDiscriminant_pos :
    0 < q1q2CircleRayDiscriminant := by
  unfold q1q2CircleRayDiscriminant
  rw [q1q2CircleRayConstant_expanded]
  nlinarith [q1q2CircleRayDot_gt_one_half]

private theorem q1q2CircleRayDiscriminant_nonneg :
    0 ≤ q1q2CircleRayDiscriminant :=
  q1q2CircleRayDiscriminant_pos.le

private theorem q1q2CircleRay_sqrt_le_dot :
    Real.sqrt q1q2CircleRayDiscriminant ≤ q1q2CircleRayDot := by
  rw [Real.sqrt_le_iff]
  exact ⟨q1q2CircleRayDot_pos.le, by
    unfold q1q2CircleRayDiscriminant
    nlinarith [q1q2CircleRayConstant_pos]⟩

/-- Near forward time along the `Q2` ray at which it hits the `Q1` circle. -/
noncomputable def q1q2CircleRayNearTime : ℝ :=
  q1q2CircleRayDot - Real.sqrt q1q2CircleRayDiscriminant

/-- Far forward time along the `Q2` ray at which it hits the `Q1` circle. -/
noncomputable def q1q2CircleRayFarTime : ℝ :=
  q1q2CircleRayDot + Real.sqrt q1q2CircleRayDiscriminant

/-- Near intersection of `circle(Q1)` with the `Q2` ray. -/
noncomputable def q1q2CircleRayNearPoint : R2 :=
  karlssonOEISQ2.anchor +
    q1q2CircleRayNearTime • karlssonOEISQ2.rayDirection

/-- Far intersection of `circle(Q1)` with the `Q2` ray. -/
noncomputable def q1q2CircleRayFarPoint : R2 :=
  karlssonOEISQ2.anchor +
    q1q2CircleRayFarTime • karlssonOEISQ2.rayDirection

theorem q1q2CircleRayNearTime_nonneg :
    0 ≤ q1q2CircleRayNearTime := by
  unfold q1q2CircleRayNearTime
  nlinarith [q1q2CircleRay_sqrt_le_dot]

theorem q1q2CircleRayFarTime_nonneg :
    0 ≤ q1q2CircleRayFarTime := by
  unfold q1q2CircleRayFarTime
  nlinarith [q1q2CircleRayDot_pos,
    Real.sqrt_nonneg q1q2CircleRayDiscriminant]

private theorem q1q2CircleRayNearTime_quadratic :
    q1q2CircleRayNearTime ^ 2 -
        2 * q1q2CircleRayDot * q1q2CircleRayNearTime +
        q1q2CircleRayConstant = 0 := by
  unfold q1q2CircleRayNearTime q1q2CircleRayDiscriminant
  have hsqrt_sq :
      (Real.sqrt
          (q1q2CircleRayDot ^ 2 - q1q2CircleRayConstant)) ^ 2 =
        q1q2CircleRayDot ^ 2 - q1q2CircleRayConstant := by
    rw [Real.sq_sqrt]
    simpa [q1q2CircleRayDiscriminant] using
      q1q2CircleRayDiscriminant_nonneg
  nlinarith [hsqrt_sq]

private theorem q1q2CircleRayFarTime_quadratic :
    q1q2CircleRayFarTime ^ 2 -
        2 * q1q2CircleRayDot * q1q2CircleRayFarTime +
        q1q2CircleRayConstant = 0 := by
  unfold q1q2CircleRayFarTime q1q2CircleRayDiscriminant
  have hsqrt_sq :
      (Real.sqrt
          (q1q2CircleRayDot ^ 2 - q1q2CircleRayConstant)) ^ 2 =
        q1q2CircleRayDot ^ 2 - q1q2CircleRayConstant := by
    rw [Real.sq_sqrt]
    simpa [q1q2CircleRayDiscriminant] using
      q1q2CircleRayDiscriminant_nonneg
  nlinarith [hsqrt_sq]

theorem q1q2CircleRayNearPoint_mem_q1_circle :
    q1q2CircleRayNearPoint ∈
      circleSet karlssonOEISQ1.center karlssonOEISQ1.radius := by
  unfold q1q2CircleRayNearPoint
  exact
    ray_point_mem_circle_of_quadratic
      (anchor := karlssonOEISQ2.anchor)
      (center := karlssonOEISQ1.center)
      (direction := karlssonOEISQ2.rayDirection)
      (radius := karlssonOEISQ1.radius)
      (dot := q1q2CircleRayDot)
      (constant := q1q2CircleRayConstant)
      rfl rfl q2_rayDirection_normSq
      q1q2CircleRayNearTime_quadratic

theorem q1q2CircleRayFarPoint_mem_q1_circle :
    q1q2CircleRayFarPoint ∈
      circleSet karlssonOEISQ1.center karlssonOEISQ1.radius := by
  unfold q1q2CircleRayFarPoint
  exact
    ray_point_mem_circle_of_quadratic
      (anchor := karlssonOEISQ2.anchor)
      (center := karlssonOEISQ1.center)
      (direction := karlssonOEISQ2.rayDirection)
      (radius := karlssonOEISQ1.radius)
      (dot := q1q2CircleRayDot)
      (constant := q1q2CircleRayConstant)
      rfl rfl q2_rayDirection_normSq
      q1q2CircleRayFarTime_quadratic

theorem q1q2CircleRayNearPoint_mem_q2_ray :
    q1q2CircleRayNearPoint ∈
      raySet karlssonOEISQ2.anchor karlssonOEISQ2.rayDirection := by
  exact ⟨q1q2CircleRayNearTime, q1q2CircleRayNearTime_nonneg, rfl⟩

theorem q1q2CircleRayFarPoint_mem_q2_ray :
    q1q2CircleRayFarPoint ∈
      raySet karlssonOEISQ2.anchor karlssonOEISQ2.rayDirection := by
  exact ⟨q1q2CircleRayFarTime, q1q2CircleRayFarTime_nonneg, rfl⟩

theorem q1q2CircleRayNearPoint_mem_euclideanCircleRaySet :
    toEuclideanR2 q1q2CircleRayNearPoint ∈
      euclideanCircleRaySet karlssonOEISQ1 karlssonOEISQ2 :=
  mem_euclideanCircleRaySet_of_mem_circleSet_of_mem_raySet
    q1q2CircleRayNearPoint_mem_q1_circle
    q1q2CircleRayNearPoint_mem_q2_ray

theorem q1q2CircleRayFarPoint_mem_euclideanCircleRaySet :
    toEuclideanR2 q1q2CircleRayFarPoint ∈
      euclideanCircleRaySet karlssonOEISQ1 karlssonOEISQ2 :=
  mem_euclideanCircleRaySet_of_mem_circleSet_of_mem_raySet
    q1q2CircleRayFarPoint_mem_q1_circle
    q1q2CircleRayFarPoint_mem_q2_ray

theorem q1q2CircleRayNearPoint_mem_base_pairIntersectionSet :
    q1q2CircleRayNearPoint ∈
      karlssonOEISBaseArrangement.pairIntersectionSet
        (1 : Fin 4) (2 : Fin 4) := by
  exact
    OEISSevenPoint.pair_mem_of_euclideanCircleRay
      (i := (1 : Fin 4)) (j := (2 : Fin 4))
      (p := q1q2CircleRayNearPoint)
      (by
        simpa [karlssonOEISBaseArrangement] using
          q1q2CircleRayNearPoint_mem_euclideanCircleRaySet)

theorem q1q2CircleRayFarPoint_mem_base_pairIntersectionSet :
    q1q2CircleRayFarPoint ∈
      karlssonOEISBaseArrangement.pairIntersectionSet
        (1 : Fin 4) (2 : Fin 4) := by
  exact
    OEISSevenPoint.pair_mem_of_euclideanCircleRay
      (i := (1 : Fin 4)) (j := (2 : Fin 4))
      (p := q1q2CircleRayFarPoint)
      (by
        simpa [karlssonOEISBaseArrangement] using
          q1q2CircleRayFarPoint_mem_euclideanCircleRaySet)

/-- The `x`-coordinate of the center of `Q2`, expressed in terms of
`alpha = 2π/15`. -/
private abbrev q1q2Q2CenterX : ℝ :=
  (23 : ℝ) / 20 + 100 * Real.sin alpha

/-- The `y`-coordinate of the center of `Q2`, expressed in terms of
`alpha = 2π/15`. -/
private abbrev q1q2Q2CenterY : ℝ :=
  (13 : ℝ) / 20 + 100 * Real.cos alpha

private theorem q1q2_q2_center_eq :
    karlssonOEISQ2.center =
      point2 q1q2Q2CenterX q1q2Q2CenterY := by
  ext i
  fin_cases i <;>
    simp [karlssonOEISQ2, EuclideanLollipop.fromAnchor, angleDirection,
      point2, q1q2Q2CenterX, q1q2Q2CenterY, q2_theta_cos,
      q2_theta_sin] <;> norm_num

/-- Positive dot coefficient in the quadratic for
`ray(Q1) ∩ circle(Q2)`. -/
private abbrev q1q2RayCircleDot : ℝ :=
  -dot2 (karlssonOEISQ1.anchor - karlssonOEISQ2.center)
    karlssonOEISQ1.rayDirection

/-- Constant term in the quadratic for `ray(Q1) ∩ circle(Q2)`. -/
private abbrev q1q2RayCircleConstant : ℝ :=
  distSq2 karlssonOEISQ1.anchor karlssonOEISQ2.center -
    karlssonOEISQ2.radius ^ 2

/-- Discriminant for `ray(Q1) ∩ circle(Q2)`. -/
private abbrev q1q2RayCircleDiscriminant : ℝ :=
  q1q2RayCircleDot ^ 2 - q1q2RayCircleConstant

private theorem q1q2RayCircleDot_expanded :
    q1q2RayCircleDot =
      (q1q2DeltaX + (100 : ℝ) * Real.sin alpha) * Real.cos theta -
        (q1q2DeltaY + (100 : ℝ) * Real.cos alpha) * Real.sin theta := by
  unfold q1q2RayCircleDot q1q2DeltaX q1q2DeltaY q1q2AnchorX
    q1q2AnchorY dot2
  simp [karlssonOEISQ1, karlssonOEISQ2, EuclideanLollipop.fromCenter,
    EuclideanLollipop.fromAnchor, angleDirection, point2, theta,
    Real.cos_neg, Real.sin_neg, q2_theta_cos, q2_theta_sin]
  ring

private theorem q1q2RayCircleConstant_expanded :
    q1q2RayCircleConstant =
      q1q2DeltaX ^ 2 + q1q2DeltaY ^ 2 +
        200 * q1q2DeltaX * Real.sin alpha +
        200 * q1q2DeltaY * Real.cos alpha := by
  unfold q1q2RayCircleConstant q1q2DeltaX q1q2DeltaY
    q1q2AnchorX q1q2AnchorY distSq2 normSq2 dot2
  simp [karlssonOEISQ1, karlssonOEISQ2, EuclideanLollipop.fromCenter,
    EuclideanLollipop.fromAnchor, angleDirection, point2, theta,
    Real.cos_neg, Real.sin_neg, q2_theta_cos, q2_theta_sin]
  ring_nf
  have htrig :
      Real.sin (Real.pi * (2 / 15 : ℝ)) ^ 2 +
          Real.cos (Real.pi * (2 / 15 : ℝ)) ^ 2 = 1 :=
    Real.sin_sq_add_cos_sq (Real.pi * (2 / 15 : ℝ))
  nlinarith [htrig]

private theorem q1q2RayCircleDot_gt_eighteen :
    (18 : ℝ) < q1q2RayCircleDot := by
  rw [q1q2RayCircleDot_expanded]
  have hbase :
      (40 : ℝ) <
        q1q2DeltaX + (100 : ℝ) * Real.sin alpha := by
    nlinarith [q1q2DeltaX_pos, sin_alpha_gt_two_div_five]
  have hleft :
      (20 : ℝ) <
        (q1q2DeltaX + (100 : ℝ) * Real.sin alpha) *
          Real.cos theta := by
    nlinarith [hbase, cos_theta_gt_one_half]
  have hsum_pos :
      0 < q1q2DeltaY + (100 : ℝ) * Real.cos alpha := by
    nlinarith [q1q2DeltaY_pos, cos_alpha_pos]
  have hsum_lt :
      q1q2DeltaY + (100 : ℝ) * Real.cos alpha < (101 : ℝ) := by
    have hcos_le : Real.cos alpha ≤ 1 := Real.cos_le_one alpha
    nlinarith [q1q2DeltaY_lt_five_eleven_div_two_thousand, hcos_le]
  have hsin_small : Real.sin theta < (1 : ℝ) / 100 := by
    simpa [theta] using sin_theta_lt_theta
  have hright :
      (q1q2DeltaY + (100 : ℝ) * Real.cos alpha) *
          Real.sin theta < (2 : ℝ) := by
    nlinarith [hsum_pos, hsum_lt, sin_theta_pos, hsin_small]
  nlinarith [hleft, hright]

private theorem q1q2RayCircleDot_pos :
    0 < q1q2RayCircleDot := by
  nlinarith [q1q2RayCircleDot_gt_eighteen]

private theorem q1q2RayCircleConstant_pos :
    0 < q1q2RayCircleConstant := by
  rw [q1q2RayCircleConstant_expanded]
  have hx :
      0 < 200 * q1q2DeltaX * Real.sin alpha := by
    nlinarith [q1q2DeltaX_pos, sin_alpha_pos]
  have hy :
      0 < 200 * q1q2DeltaY * Real.cos alpha := by
    nlinarith [q1q2DeltaY_pos, cos_alpha_pos]
  nlinarith [sq_nonneg q1q2DeltaX, sq_nonneg q1q2DeltaY, hx, hy]

private theorem q1q2RayCircleConstant_lt_three_hundred :
    q1q2RayCircleConstant < (300 : ℝ) := by
  rw [q1q2RayCircleConstant_expanded]
  have hx_sq : q1q2DeltaX ^ 2 < 1 := by
    nlinarith [q1q2DeltaX_pos, q1q2DeltaX_lt_one]
  have hy_sq : q1q2DeltaY ^ 2 < 1 := by
    nlinarith [q1q2DeltaY_pos, q1q2DeltaY_lt_one]
  have hxsin :
      q1q2DeltaX * Real.sin alpha < 1 := by
    have hsin_le : Real.sin alpha ≤ 1 := Real.sin_le_one alpha
    nlinarith [q1q2DeltaX_pos, q1q2DeltaX_lt_one,
      sin_alpha_pos, hsin_le]
  have hycos :
      q1q2DeltaY * Real.cos alpha < (511 : ℝ) / 2000 := by
    have hcos_le : Real.cos alpha ≤ 1 := Real.cos_le_one alpha
    nlinarith [q1q2DeltaY_pos,
      q1q2DeltaY_lt_five_eleven_div_two_thousand,
      cos_alpha_pos, hcos_le]
  nlinarith [hx_sq, hy_sq, hxsin, hycos]

private theorem q1q2RayCircleDiscriminant_pos :
    0 < q1q2RayCircleDiscriminant := by
  unfold q1q2RayCircleDiscriminant
  nlinarith [q1q2RayCircleDot_gt_eighteen,
    q1q2RayCircleConstant_lt_three_hundred]

private theorem q1q2RayCircleDiscriminant_nonneg :
    0 ≤ q1q2RayCircleDiscriminant :=
  q1q2RayCircleDiscriminant_pos.le

private theorem q1q2RayCircle_sqrt_le_dot :
    Real.sqrt q1q2RayCircleDiscriminant ≤ q1q2RayCircleDot := by
  rw [Real.sqrt_le_iff]
  exact ⟨q1q2RayCircleDot_pos.le, by
    unfold q1q2RayCircleDiscriminant
    nlinarith [q1q2RayCircleConstant_pos]⟩

/-- Near forward time along the `Q1` ray at which it hits the `Q2` circle. -/
noncomputable def q1q2RayCircleNearTime : ℝ :=
  q1q2RayCircleDot - Real.sqrt q1q2RayCircleDiscriminant

/-- Far forward time along the `Q1` ray at which it hits the `Q2` circle. -/
noncomputable def q1q2RayCircleFarTime : ℝ :=
  q1q2RayCircleDot + Real.sqrt q1q2RayCircleDiscriminant

/-- Near intersection of the `Q1` ray with `circle(Q2)`. -/
noncomputable def q1q2RayCircleNearPoint : R2 :=
  karlssonOEISQ1.anchor +
    q1q2RayCircleNearTime • karlssonOEISQ1.rayDirection

/-- Far intersection of the `Q1` ray with `circle(Q2)`. -/
noncomputable def q1q2RayCircleFarPoint : R2 :=
  karlssonOEISQ1.anchor +
    q1q2RayCircleFarTime • karlssonOEISQ1.rayDirection

theorem q1q2RayCircleNearTime_nonneg :
    0 ≤ q1q2RayCircleNearTime := by
  unfold q1q2RayCircleNearTime
  nlinarith [q1q2RayCircle_sqrt_le_dot]

theorem q1q2RayCircleFarTime_nonneg :
    0 ≤ q1q2RayCircleFarTime := by
  unfold q1q2RayCircleFarTime
  nlinarith [q1q2RayCircleDot_pos,
    Real.sqrt_nonneg q1q2RayCircleDiscriminant]

private theorem q1q2RayCircleNearTime_quadratic :
    q1q2RayCircleNearTime ^ 2 -
        2 * q1q2RayCircleDot * q1q2RayCircleNearTime +
        q1q2RayCircleConstant = 0 := by
  unfold q1q2RayCircleNearTime q1q2RayCircleDiscriminant
  have hsqrt_sq :
      (Real.sqrt
          (q1q2RayCircleDot ^ 2 - q1q2RayCircleConstant)) ^ 2 =
        q1q2RayCircleDot ^ 2 - q1q2RayCircleConstant := by
    rw [Real.sq_sqrt]
    simpa [q1q2RayCircleDiscriminant] using
      q1q2RayCircleDiscriminant_nonneg
  nlinarith [hsqrt_sq]

private theorem q1q2RayCircleFarTime_quadratic :
    q1q2RayCircleFarTime ^ 2 -
        2 * q1q2RayCircleDot * q1q2RayCircleFarTime +
        q1q2RayCircleConstant = 0 := by
  unfold q1q2RayCircleFarTime q1q2RayCircleDiscriminant
  have hsqrt_sq :
      (Real.sqrt
          (q1q2RayCircleDot ^ 2 - q1q2RayCircleConstant)) ^ 2 =
        q1q2RayCircleDot ^ 2 - q1q2RayCircleConstant := by
    rw [Real.sq_sqrt]
    simpa [q1q2RayCircleDiscriminant] using
      q1q2RayCircleDiscriminant_nonneg
  nlinarith [hsqrt_sq]

theorem q1q2RayCircleNearPoint_mem_q1_ray :
    q1q2RayCircleNearPoint ∈
      raySet karlssonOEISQ1.anchor karlssonOEISQ1.rayDirection := by
  exact ⟨q1q2RayCircleNearTime, q1q2RayCircleNearTime_nonneg, rfl⟩

theorem q1q2RayCircleFarPoint_mem_q1_ray :
    q1q2RayCircleFarPoint ∈
      raySet karlssonOEISQ1.anchor karlssonOEISQ1.rayDirection := by
  exact ⟨q1q2RayCircleFarTime, q1q2RayCircleFarTime_nonneg, rfl⟩

theorem q1q2RayCircleNearPoint_mem_q2_circle :
    q1q2RayCircleNearPoint ∈
      circleSet karlssonOEISQ2.center karlssonOEISQ2.radius := by
  unfold q1q2RayCircleNearPoint
  exact
    ray_point_mem_circle_of_quadratic
      (anchor := karlssonOEISQ1.anchor)
      (center := karlssonOEISQ2.center)
      (direction := karlssonOEISQ1.rayDirection)
      (radius := karlssonOEISQ2.radius)
      (dot := q1q2RayCircleDot)
      (constant := q1q2RayCircleConstant)
      rfl rfl q1_rayDirection_normSq
      q1q2RayCircleNearTime_quadratic

theorem q1q2RayCircleFarPoint_mem_q2_circle :
    q1q2RayCircleFarPoint ∈
      circleSet karlssonOEISQ2.center karlssonOEISQ2.radius := by
  unfold q1q2RayCircleFarPoint
  exact
    ray_point_mem_circle_of_quadratic
      (anchor := karlssonOEISQ1.anchor)
      (center := karlssonOEISQ2.center)
      (direction := karlssonOEISQ1.rayDirection)
      (radius := karlssonOEISQ2.radius)
      (dot := q1q2RayCircleDot)
      (constant := q1q2RayCircleConstant)
      rfl rfl q1_rayDirection_normSq
      q1q2RayCircleFarTime_quadratic

theorem q1q2RayCircleNearPoint_mem_euclideanRayCircleSet :
    toEuclideanR2 q1q2RayCircleNearPoint ∈
      euclideanRayCircleSet karlssonOEISQ1 karlssonOEISQ2 :=
  mem_euclideanRayCircleSet_of_mem_raySet_of_mem_circleSet
    q1q2RayCircleNearPoint_mem_q1_ray
    q1q2RayCircleNearPoint_mem_q2_circle

theorem q1q2RayCircleFarPoint_mem_euclideanRayCircleSet :
    toEuclideanR2 q1q2RayCircleFarPoint ∈
      euclideanRayCircleSet karlssonOEISQ1 karlssonOEISQ2 :=
  mem_euclideanRayCircleSet_of_mem_raySet_of_mem_circleSet
    q1q2RayCircleFarPoint_mem_q1_ray
    q1q2RayCircleFarPoint_mem_q2_circle

theorem q1q2RayCircleNearPoint_mem_base_pairIntersectionSet :
    q1q2RayCircleNearPoint ∈
      karlssonOEISBaseArrangement.pairIntersectionSet
        (1 : Fin 4) (2 : Fin 4) := by
  exact
    OEISSevenPoint.pair_mem_of_euclideanRayCircle
      (i := (1 : Fin 4)) (j := (2 : Fin 4))
      (p := q1q2RayCircleNearPoint)
      (by
        simpa [karlssonOEISBaseArrangement] using
          q1q2RayCircleNearPoint_mem_euclideanRayCircleSet)

theorem q1q2RayCircleFarPoint_mem_base_pairIntersectionSet :
    q1q2RayCircleFarPoint ∈
      karlssonOEISBaseArrangement.pairIntersectionSet
        (1 : Fin 4) (2 : Fin 4) := by
  exact
    OEISSevenPoint.pair_mem_of_euclideanRayCircle
      (i := (1 : Fin 4)) (j := (2 : Fin 4))
      (p := q1q2RayCircleFarPoint)
      (by
        simpa [karlssonOEISBaseArrangement] using
          q1q2RayCircleFarPoint_mem_euclideanRayCircleSet)

/-- The `x`-coordinate of the center of `Q1`. -/
private abbrev q1q2Q1CenterX : ℝ :=
  (45 : ℝ) / 100

/-- The `y`-coordinate of the center of `Q1`. -/
private abbrev q1q2Q1CenterY : ℝ :=
  (4 : ℝ) / 10

private theorem q1q2_q1_center_eq :
    karlssonOEISQ1.center =
      point2 q1q2Q1CenterX q1q2Q1CenterY := by
  ext i
  fin_cases i <;>
    simp [karlssonOEISQ1, EuclideanLollipop.fromCenter, point2,
      q1q2Q1CenterX, q1q2Q1CenterY]

/-- Center displacement from `Q1`'s circle center to `Q2`'s circle center,
x-coordinate. -/
private abbrev q1q2CircleCircleDX : ℝ :=
  q1q2Q2CenterX - q1q2Q1CenterX

/-- Center displacement from `Q1`'s circle center to `Q2`'s circle center,
y-coordinate. -/
private abbrev q1q2CircleCircleDY : ℝ :=
  q1q2Q2CenterY - q1q2Q1CenterY

/-- Squared distance between the two circle centers for `(Q1,Q2)`. -/
private abbrev q1q2CircleCircleD : ℝ :=
  q1q2CircleCircleDX ^ 2 + q1q2CircleCircleDY ^ 2

/-- Radical-axis dot coordinate for the two circle-circle intersections. -/
private abbrev q1q2CircleCircleA : ℝ :=
  (q1q2CircleCircleD + ((11 : ℝ) / 20) ^ 2 - (100 : ℝ) ^ 2) / 2

/-- Squared perpendicular height of the two circle-circle intersections. -/
private abbrev q1q2CircleCircleH2 : ℝ :=
  ((11 : ℝ) / 20) ^ 2 * q1q2CircleCircleD -
    q1q2CircleCircleA ^ 2

private theorem q1q2CircleCircleD_expanded :
    q1q2CircleCircleD =
      (10000 : ℝ) + 140 * Real.sin alpha +
        50 * Real.cos alpha + (221 : ℝ) / 400 := by
  unfold q1q2CircleCircleD q1q2CircleCircleDX q1q2CircleCircleDY
    q1q2Q2CenterX q1q2Q2CenterY q1q2Q1CenterX q1q2Q1CenterY
  ring_nf
  have htrig :
      Real.sin (Real.pi * (2 / 15 : ℝ)) ^ 2 +
          Real.cos (Real.pi * (2 / 15 : ℝ)) ^ 2 = 1 :=
    Real.sin_sq_add_cos_sq (Real.pi * (2 / 15 : ℝ))
  nlinarith [htrig]

private theorem q1q2CircleCircleD_gt_radius_diff_sq :
    ((1989 : ℝ) / 20) ^ 2 < q1q2CircleCircleD := by
  rw [q1q2CircleCircleD_expanded]
  nlinarith [sin_alpha_pos, cos_alpha_pos]

private theorem q1q2CircleCircleD_lt_radius_sum_sq :
    q1q2CircleCircleD < ((2011 : ℝ) / 20) ^ 2 := by
  rw [q1q2CircleCircleD_expanded]
  have hcos_le : Real.cos alpha ≤ 1 := Real.cos_le_one alpha
  nlinarith [sin_alpha_lt_twenty_one_div_fifty, hcos_le]

/-- The private center-distance abbreviation is exactly the squared distance
between the `Q1` and `Q2` circle centers. -/
theorem q1q2CircleCircleD_eq_distSq2_centers :
    q1q2CircleCircleD =
      distSq2 karlssonOEISQ1.center karlssonOEISQ2.center := by
  rw [q1q2_q1_center_eq, q1q2_q2_center_eq]
  simp [q1q2CircleCircleD, q1q2CircleCircleDX, q1q2CircleCircleDY,
    q1q2Q1CenterX, q1q2Q1CenterY, q1q2Q2CenterX, q1q2Q2CenterY,
    distSq2, normSq2, dot2, point2]
  ring

/-- The `Q1,Q2` circle pair satisfies Paulsen's strict obtuse-intersection
distance condition, hence is not intriguing. -/
theorem q1q2_circleObtuseCondition :
    TheoremOneEndToEnd.PaulsenLinearAlgebra.circleObtuseCondition
      karlssonOEISQ1.radius karlssonOEISQ2.radius
      karlssonOEISQ1.center karlssonOEISQ2.center := by
  unfold TheoremOneEndToEnd.PaulsenLinearAlgebra.circleObtuseCondition
  constructor
  · rw [← q1q2CircleCircleD_eq_distSq2_centers]
    rw [q1q2CircleCircleD_expanded]
    have hrad :
        karlssonOEISQ1.radius ^ 2 + karlssonOEISQ2.radius ^ 2 =
          (10000 : ℝ) + (121 : ℝ) / 400 := by
      norm_num [karlssonOEISQ1, karlssonOEISQ2,
        EuclideanLollipop.fromCenter, EuclideanLollipop.fromAnchor]
    rw [hrad]
    nlinarith [sin_alpha_pos, cos_alpha_pos]
  · rw [← q1q2CircleCircleD_eq_distSq2_centers]
    have hsum :
        (karlssonOEISQ1.radius + karlssonOEISQ2.radius) ^ 2 =
          ((2011 : ℝ) / 20) ^ 2 := by
      norm_num [karlssonOEISQ1, karlssonOEISQ2,
        EuclideanLollipop.fromCenter, EuclideanLollipop.fromAnchor]
    rw [hsum]
    exact q1q2CircleCircleD_lt_radius_sum_sq

/-- Pair-level form: `(Q1,Q2)` is not intriguing. -/
theorem q1q2_not_circleIntriguingPair :
    ¬ TheoremOneEndToEnd.PaulsenLinearAlgebra.circleIntriguingPair
      karlssonOEISQ1.radius karlssonOEISQ2.radius
      karlssonOEISQ1.center karlssonOEISQ2.center := by
  classical
  exact not_not.mpr q1q2_circleObtuseCondition

private theorem q1q2CircleCircleD_pos :
    0 < q1q2CircleCircleD := by
  nlinarith [q1q2CircleCircleD_gt_radius_diff_sq]

private theorem q1q2CircleCircleD_ne :
    q1q2CircleCircleD ≠ 0 :=
  q1q2CircleCircleD_pos.ne'

private theorem q1q2CircleCircleH2_pos :
    0 < q1q2CircleCircleH2 := by
  unfold q1q2CircleCircleH2 q1q2CircleCircleA
  have hprod :
      0 <
        (((2011 : ℝ) / 20) ^ 2 - q1q2CircleCircleD) *
          (q1q2CircleCircleD - ((1989 : ℝ) / 20) ^ 2) :=
    mul_pos (sub_pos.2 q1q2CircleCircleD_lt_radius_sum_sq)
      (sub_pos.2 q1q2CircleCircleD_gt_radius_diff_sq)
  nlinarith [hprod]

private theorem q1q2CircleCircleH2_nonneg :
    0 ≤ q1q2CircleCircleH2 :=
  q1q2CircleCircleH2_pos.le

/-- One of the two intersections of `circle(Q1)` and `circle(Q2)`. -/
noncomputable def q1q2CircleCircleUpperPoint : R2 :=
  point2
    (q1q2Q1CenterX +
      (q1q2CircleCircleA * q1q2CircleCircleDX -
        Real.sqrt q1q2CircleCircleH2 * q1q2CircleCircleDY) /
        q1q2CircleCircleD)
    (q1q2Q1CenterY +
      (q1q2CircleCircleA * q1q2CircleCircleDY +
        Real.sqrt q1q2CircleCircleH2 * q1q2CircleCircleDX) /
        q1q2CircleCircleD)

/-- The other intersection of `circle(Q1)` and `circle(Q2)`. -/
noncomputable def q1q2CircleCircleLowerPoint : R2 :=
  point2
    (q1q2Q1CenterX +
      (q1q2CircleCircleA * q1q2CircleCircleDX +
        Real.sqrt q1q2CircleCircleH2 * q1q2CircleCircleDY) /
        q1q2CircleCircleD)
    (q1q2Q1CenterY +
      (q1q2CircleCircleA * q1q2CircleCircleDY -
        Real.sqrt q1q2CircleCircleH2 * q1q2CircleCircleDX) /
        q1q2CircleCircleD)

private theorem q1q2CircleCircle_sqrt_sq :
    (Real.sqrt q1q2CircleCircleH2) ^ 2 =
      q1q2CircleCircleH2 :=
  Real.sq_sqrt q1q2CircleCircleH2_nonneg

private theorem q1q2CircleCircle_A_sq_add_H_sq_q1 :
    q1q2CircleCircleA ^ 2 +
        (Real.sqrt q1q2CircleCircleH2) ^ 2 =
      ((11 : ℝ) / 20) ^ 2 * q1q2CircleCircleD := by
  rw [q1q2CircleCircle_sqrt_sq]
  unfold q1q2CircleCircleH2
  ring

private theorem q1q2CircleCircle_A_sub_D_sq_add_H_sq_q2 :
    (q1q2CircleCircleA - q1q2CircleCircleD) ^ 2 +
        (Real.sqrt q1q2CircleCircleH2) ^ 2 =
      (100 : ℝ) ^ 2 * q1q2CircleCircleD := by
  rw [q1q2CircleCircle_sqrt_sq]
  unfold q1q2CircleCircleH2 q1q2CircleCircleA
  ring

private theorem circleCircleUpper_left_algebra
    (dx dy D A H r : ℝ)
    (hD : D = dx ^ 2 + dy ^ 2)
    (hAH : A ^ 2 + H ^ 2 = r ^ 2 * D)
    (hDne : D ≠ 0) :
    ((A * dx - H * dy) / D) * ((A * dx - H * dy) / D) +
      ((A * dy + H * dx) / D) * ((A * dy + H * dx) / D) =
      r ^ 2 := by
  field_simp [hDne]
  nlinarith [hD, hAH]

private theorem circleCircleLower_left_algebra
    (dx dy D A H r : ℝ)
    (hD : D = dx ^ 2 + dy ^ 2)
    (hAH : A ^ 2 + H ^ 2 = r ^ 2 * D)
    (hDne : D ≠ 0) :
    ((A * dx + H * dy) / D) * ((A * dx + H * dy) / D) +
      ((A * dy - H * dx) / D) * ((A * dy - H * dx) / D) =
      r ^ 2 := by
  field_simp [hDne]
  nlinarith [hD, hAH]

private theorem circleCircleUpper_right_algebra
    (dx dy D A H r : ℝ)
    (hD : D = dx ^ 2 + dy ^ 2)
    (hAH : (A - D) ^ 2 + H ^ 2 = r ^ 2 * D)
    (hDne : D ≠ 0) :
    ((A * dx - H * dy) / D - dx) *
        ((A * dx - H * dy) / D - dx) +
      ((A * dy + H * dx) / D - dy) *
        ((A * dy + H * dx) / D - dy) =
      r ^ 2 := by
  field_simp [hDne]
  nlinarith [hD, hAH]

private theorem circleCircleLower_right_algebra
    (dx dy D A H r : ℝ)
    (hD : D = dx ^ 2 + dy ^ 2)
    (hAH : (A - D) ^ 2 + H ^ 2 = r ^ 2 * D)
    (hDne : D ≠ 0) :
    ((A * dx + H * dy) / D - dx) *
        ((A * dx + H * dy) / D - dx) +
      ((A * dy - H * dx) / D - dy) *
        ((A * dy - H * dx) / D - dy) =
      r ^ 2 := by
  field_simp [hDne]
  nlinarith [hD, hAH]

private theorem q1q2CircleCircleUpper_q1_coordinate :
    ((q1q2CircleCircleA * q1q2CircleCircleDX -
          Real.sqrt q1q2CircleCircleH2 * q1q2CircleCircleDY) /
        q1q2CircleCircleD) *
        ((q1q2CircleCircleA * q1q2CircleCircleDX -
            Real.sqrt q1q2CircleCircleH2 * q1q2CircleCircleDY) /
          q1q2CircleCircleD) +
      ((q1q2CircleCircleA * q1q2CircleCircleDY +
          Real.sqrt q1q2CircleCircleH2 * q1q2CircleCircleDX) /
        q1q2CircleCircleD) *
        ((q1q2CircleCircleA * q1q2CircleCircleDY +
            Real.sqrt q1q2CircleCircleH2 * q1q2CircleCircleDX) /
          q1q2CircleCircleD) =
      ((11 : ℝ) / 20) ^ 2 := by
  exact circleCircleUpper_left_algebra
    q1q2CircleCircleDX q1q2CircleCircleDY q1q2CircleCircleD
    q1q2CircleCircleA (Real.sqrt q1q2CircleCircleH2) ((11 : ℝ) / 20)
    rfl q1q2CircleCircle_A_sq_add_H_sq_q1 q1q2CircleCircleD_ne

private theorem q1q2CircleCircleLower_q1_coordinate :
    ((q1q2CircleCircleA * q1q2CircleCircleDX +
          Real.sqrt q1q2CircleCircleH2 * q1q2CircleCircleDY) /
        q1q2CircleCircleD) *
        ((q1q2CircleCircleA * q1q2CircleCircleDX +
            Real.sqrt q1q2CircleCircleH2 * q1q2CircleCircleDY) /
          q1q2CircleCircleD) +
      ((q1q2CircleCircleA * q1q2CircleCircleDY -
          Real.sqrt q1q2CircleCircleH2 * q1q2CircleCircleDX) /
        q1q2CircleCircleD) *
        ((q1q2CircleCircleA * q1q2CircleCircleDY -
            Real.sqrt q1q2CircleCircleH2 * q1q2CircleCircleDX) /
          q1q2CircleCircleD) =
      ((11 : ℝ) / 20) ^ 2 := by
  exact circleCircleLower_left_algebra
    q1q2CircleCircleDX q1q2CircleCircleDY q1q2CircleCircleD
    q1q2CircleCircleA (Real.sqrt q1q2CircleCircleH2) ((11 : ℝ) / 20)
    rfl q1q2CircleCircle_A_sq_add_H_sq_q1 q1q2CircleCircleD_ne

private theorem q1q2CircleCircleUpper_q2_coordinate :
    (q1q2Q1CenterX +
          (q1q2CircleCircleA * q1q2CircleCircleDX -
              Real.sqrt q1q2CircleCircleH2 * q1q2CircleCircleDY) /
            q1q2CircleCircleD -
        q1q2Q2CenterX) *
        (q1q2Q1CenterX +
            (q1q2CircleCircleA * q1q2CircleCircleDX -
                Real.sqrt q1q2CircleCircleH2 * q1q2CircleCircleDY) /
              q1q2CircleCircleD -
          q1q2Q2CenterX) +
      (q1q2Q1CenterY +
            (q1q2CircleCircleA * q1q2CircleCircleDY +
                Real.sqrt q1q2CircleCircleH2 * q1q2CircleCircleDX) /
              q1q2CircleCircleD -
          q1q2Q2CenterY) *
        (q1q2Q1CenterY +
            (q1q2CircleCircleA * q1q2CircleCircleDY +
                Real.sqrt q1q2CircleCircleH2 * q1q2CircleCircleDX) /
              q1q2CircleCircleD -
          q1q2Q2CenterY) =
      (100 : ℝ) ^ 2 := by
  have h := circleCircleUpper_right_algebra
    q1q2CircleCircleDX q1q2CircleCircleDY q1q2CircleCircleD
    q1q2CircleCircleA (Real.sqrt q1q2CircleCircleH2) 100
    rfl q1q2CircleCircle_A_sub_D_sq_add_H_sq_q2 q1q2CircleCircleD_ne
  unfold q1q2CircleCircleDX q1q2CircleCircleDY at h
  convert h using 1
  all_goals ring

private theorem q1q2CircleCircleLower_q2_coordinate :
    (q1q2Q1CenterX +
          (q1q2CircleCircleA * q1q2CircleCircleDX +
              Real.sqrt q1q2CircleCircleH2 * q1q2CircleCircleDY) /
            q1q2CircleCircleD -
        q1q2Q2CenterX) *
        (q1q2Q1CenterX +
            (q1q2CircleCircleA * q1q2CircleCircleDX +
                Real.sqrt q1q2CircleCircleH2 * q1q2CircleCircleDY) /
              q1q2CircleCircleD -
          q1q2Q2CenterX) +
      (q1q2Q1CenterY +
            (q1q2CircleCircleA * q1q2CircleCircleDY -
                Real.sqrt q1q2CircleCircleH2 * q1q2CircleCircleDX) /
              q1q2CircleCircleD -
          q1q2Q2CenterY) *
        (q1q2Q1CenterY +
            (q1q2CircleCircleA * q1q2CircleCircleDY -
                Real.sqrt q1q2CircleCircleH2 * q1q2CircleCircleDX) /
              q1q2CircleCircleD -
          q1q2Q2CenterY) =
      (100 : ℝ) ^ 2 := by
  have h := circleCircleLower_right_algebra
    q1q2CircleCircleDX q1q2CircleCircleDY q1q2CircleCircleD
    q1q2CircleCircleA (Real.sqrt q1q2CircleCircleH2) 100
    rfl q1q2CircleCircle_A_sub_D_sq_add_H_sq_q2 q1q2CircleCircleD_ne
  unfold q1q2CircleCircleDX q1q2CircleCircleDY at h
  convert h using 1
  all_goals ring

theorem q1q2CircleCircleUpperPoint_mem_q1_circle :
    q1q2CircleCircleUpperPoint ∈
      circleSet karlssonOEISQ1.center karlssonOEISQ1.radius := by
  unfold q1q2CircleCircleUpperPoint circleSet distSq2 normSq2 dot2
  rw [q1q2_q1_center_eq]
  simp [karlssonOEISQ1, EuclideanLollipop.fromCenter, point2]
  convert q1q2CircleCircleUpper_q1_coordinate using 1
  all_goals norm_num

theorem q1q2CircleCircleLowerPoint_mem_q1_circle :
    q1q2CircleCircleLowerPoint ∈
      circleSet karlssonOEISQ1.center karlssonOEISQ1.radius := by
  unfold q1q2CircleCircleLowerPoint circleSet distSq2 normSq2 dot2
  rw [q1q2_q1_center_eq]
  simp [karlssonOEISQ1, EuclideanLollipop.fromCenter, point2]
  convert q1q2CircleCircleLower_q1_coordinate using 1
  all_goals norm_num

theorem q1q2CircleCircleUpperPoint_mem_q2_circle :
    q1q2CircleCircleUpperPoint ∈
      circleSet karlssonOEISQ2.center karlssonOEISQ2.radius := by
  unfold q1q2CircleCircleUpperPoint circleSet distSq2 normSq2 dot2
  rw [q1q2_q2_center_eq]
  simp [karlssonOEISQ2, EuclideanLollipop.fromAnchor, point2]
  exact q1q2CircleCircleUpper_q2_coordinate

theorem q1q2CircleCircleLowerPoint_mem_q2_circle :
    q1q2CircleCircleLowerPoint ∈
      circleSet karlssonOEISQ2.center karlssonOEISQ2.radius := by
  unfold q1q2CircleCircleLowerPoint circleSet distSq2 normSq2 dot2
  rw [q1q2_q2_center_eq]
  simp [karlssonOEISQ2, EuclideanLollipop.fromAnchor, point2]
  exact q1q2CircleCircleLower_q2_coordinate

theorem q1q2CircleCircleUpperPoint_mem_euclideanCircleCircleSet :
    toEuclideanR2 q1q2CircleCircleUpperPoint ∈
      euclideanCircleCircleSet karlssonOEISQ1 karlssonOEISQ2 :=
  mem_euclideanCircleCircleSet_of_mem_circleSets
    q1q2CircleCircleUpperPoint_mem_q1_circle
    q1q2CircleCircleUpperPoint_mem_q2_circle

theorem q1q2CircleCircleLowerPoint_mem_euclideanCircleCircleSet :
    toEuclideanR2 q1q2CircleCircleLowerPoint ∈
      euclideanCircleCircleSet karlssonOEISQ1 karlssonOEISQ2 :=
  mem_euclideanCircleCircleSet_of_mem_circleSets
    q1q2CircleCircleLowerPoint_mem_q1_circle
    q1q2CircleCircleLowerPoint_mem_q2_circle

theorem q1q2CircleCircleUpperPoint_mem_base_pairIntersectionSet :
    q1q2CircleCircleUpperPoint ∈
      karlssonOEISBaseArrangement.pairIntersectionSet
        (1 : Fin 4) (2 : Fin 4) := by
  exact
    OEISSevenPoint.pair_mem_of_euclideanCircleCircle
      (i := (1 : Fin 4)) (j := (2 : Fin 4))
      (p := q1q2CircleCircleUpperPoint)
      (by
        simpa [karlssonOEISBaseArrangement] using
          q1q2CircleCircleUpperPoint_mem_euclideanCircleCircleSet)

theorem q1q2CircleCircleLowerPoint_mem_base_pairIntersectionSet :
    q1q2CircleCircleLowerPoint ∈
      karlssonOEISBaseArrangement.pairIntersectionSet
        (1 : Fin 4) (2 : Fin 4) := by
  exact
    OEISSevenPoint.pair_mem_of_euclideanCircleCircle
      (i := (1 : Fin 4)) (j := (2 : Fin 4))
      (p := q1q2CircleCircleLowerPoint)
      (by
        simpa [karlssonOEISBaseArrangement] using
          q1q2CircleCircleLowerPoint_mem_euclideanCircleCircleSet)

private theorem q1q2CircleRay_sqrt_lt_dot :
    Real.sqrt q1q2CircleRayDiscriminant < q1q2CircleRayDot := by
  rw [Real.sqrt_lt q1q2CircleRayDiscriminant_nonneg
    q1q2CircleRayDot_pos.le]
  unfold q1q2CircleRayDiscriminant
  nlinarith [q1q2CircleRayConstant_pos]

theorem q1q2CircleRayNearTime_pos :
    0 < q1q2CircleRayNearTime := by
  unfold q1q2CircleRayNearTime
  nlinarith [q1q2CircleRay_sqrt_lt_dot]

theorem q1q2CircleRayFarTime_pos :
    0 < q1q2CircleRayFarTime := by
  unfold q1q2CircleRayFarTime
  nlinarith [q1q2CircleRayDot_pos,
    Real.sqrt_nonneg q1q2CircleRayDiscriminant]

private theorem q1q2RayCircle_sqrt_lt_dot :
    Real.sqrt q1q2RayCircleDiscriminant < q1q2RayCircleDot := by
  rw [Real.sqrt_lt q1q2RayCircleDiscriminant_nonneg
    q1q2RayCircleDot_pos.le]
  unfold q1q2RayCircleDiscriminant
  nlinarith [q1q2RayCircleConstant_pos]

theorem q1q2RayCircleNearTime_pos :
    0 < q1q2RayCircleNearTime := by
  unfold q1q2RayCircleNearTime
  nlinarith [q1q2RayCircle_sqrt_lt_dot]

theorem q1q2RayCircleFarTime_pos :
    0 < q1q2RayCircleFarTime := by
  unfold q1q2RayCircleFarTime
  nlinarith [q1q2RayCircleDot_pos,
    Real.sqrt_nonneg q1q2RayCircleDiscriminant]

private theorem q1_ray_point_not_mem_q1_circle_of_time_pos
    {t : ℝ} (ht : 0 < t) :
    karlssonOEISQ1.anchor + t • karlssonOEISQ1.rayDirection ∉
      circleSet karlssonOEISQ1.center karlssonOEISQ1.radius := by
  intro hp
  unfold circleSet distSq2 normSq2 dot2 at hp
  simp [karlssonOEISQ1, EuclideanLollipop.fromCenter, angleDirection,
    point2, Real.cos_neg, Real.sin_neg] at hp
  ring_nf at hp
  have htrig :
      Real.cos ((1 : ℝ) / 100) ^ 2 +
          Real.sin ((1 : ℝ) / 100) ^ 2 = 1 :=
    Real.cos_sq_add_sin_sq ((1 : ℝ) / 100)
  nlinarith [htrig, ht, hp]

private theorem q2_ray_point_not_mem_q2_circle_of_time_pos
    {t : ℝ} (ht : 0 < t) :
    karlssonOEISQ2.anchor + t • karlssonOEISQ2.rayDirection ∉
      circleSet karlssonOEISQ2.center karlssonOEISQ2.radius := by
  intro hp
  unfold circleSet distSq2 normSq2 dot2 at hp
  simp [karlssonOEISQ2, EuclideanLollipop.fromAnchor, angleDirection,
    point2, q2_theta_cos, q2_theta_sin] at hp
  ring_nf at hp
  have htrig :
      Real.sin (Real.pi * (2 / 15 : ℝ)) ^ 2 +
          Real.cos (Real.pi * (2 / 15 : ℝ)) ^ 2 = 1 :=
    Real.sin_sq_add_cos_sq (Real.pi * (2 / 15 : ℝ))
  nlinarith [htrig, ht, hp]

theorem q1q2CircleRayNearPoint_not_mem_q2_circle :
    q1q2CircleRayNearPoint ∉
      circleSet karlssonOEISQ2.center karlssonOEISQ2.radius := by
  unfold q1q2CircleRayNearPoint
  exact q2_ray_point_not_mem_q2_circle_of_time_pos
    q1q2CircleRayNearTime_pos

theorem q1q2CircleRayFarPoint_not_mem_q2_circle :
    q1q2CircleRayFarPoint ∉
      circleSet karlssonOEISQ2.center karlssonOEISQ2.radius := by
  unfold q1q2CircleRayFarPoint
  exact q2_ray_point_not_mem_q2_circle_of_time_pos
    q1q2CircleRayFarTime_pos

theorem q1q2RayCircleNearPoint_not_mem_q1_circle :
    q1q2RayCircleNearPoint ∉
      circleSet karlssonOEISQ1.center karlssonOEISQ1.radius := by
  unfold q1q2RayCircleNearPoint
  exact q1_ray_point_not_mem_q1_circle_of_time_pos
    q1q2RayCircleNearTime_pos

theorem q1q2RayCircleFarPoint_not_mem_q1_circle :
    q1q2RayCircleFarPoint ∉
      circleSet karlssonOEISQ1.center karlssonOEISQ1.radius := by
  unfold q1q2RayCircleFarPoint
  exact q1_ray_point_not_mem_q1_circle_of_time_pos
    q1q2RayCircleFarTime_pos

theorem q1q2RayRayPoint_not_mem_q1_circle :
    q1q2RayRayPoint ∉
      circleSet karlssonOEISQ1.center karlssonOEISQ1.radius := by
  unfold q1q2RayRayPoint
  exact q1_ray_point_not_mem_q1_circle_of_time_pos
    q1q2RayRayTimeQ1_pos

theorem q1q2RayRayPoint_not_mem_q2_circle :
    q1q2RayRayPoint ∉
      circleSet karlssonOEISQ2.center karlssonOEISQ2.radius := by
  rw [q1q2RayRayPoint_eq_q2_ray_expression]
  exact q2_ray_point_not_mem_q2_circle_of_time_pos
    q1q2RayRayTimeQ2_pos

private theorem q1q2CircleCircleDX_pos :
    0 < q1q2CircleCircleDX := by
  unfold q1q2CircleCircleDX q1q2Q2CenterX q1q2Q1CenterX
  nlinarith [sin_alpha_pos]

theorem q1q2CircleCircleUpperPoint_ne_lower :
    q1q2CircleCircleUpperPoint ≠ q1q2CircleCircleLowerPoint := by
  intro h
  have hy := congr_fun h 1
  unfold q1q2CircleCircleUpperPoint q1q2CircleCircleLowerPoint at hy
  simp [point2] at hy
  have hH : 0 < Real.sqrt q1q2CircleCircleH2 :=
    Real.sqrt_pos.2 q1q2CircleCircleH2_pos
  have hdiff :
      ((q1q2CircleCircleA * q1q2CircleCircleDY +
            Real.sqrt q1q2CircleCircleH2 * q1q2CircleCircleDX) /
          q1q2CircleCircleD) -
        ((q1q2CircleCircleA * q1q2CircleCircleDY -
            Real.sqrt q1q2CircleCircleH2 * q1q2CircleCircleDX) /
          q1q2CircleCircleD) = 0 := by
    nlinarith [hy]
  have hdiff_eval :
      ((q1q2CircleCircleA * q1q2CircleCircleDY +
            Real.sqrt q1q2CircleCircleH2 * q1q2CircleCircleDX) /
          q1q2CircleCircleD) -
        ((q1q2CircleCircleA * q1q2CircleCircleDY -
            Real.sqrt q1q2CircleCircleH2 * q1q2CircleCircleDX) /
          q1q2CircleCircleD) =
        (2 * Real.sqrt q1q2CircleCircleH2 *
            q1q2CircleCircleDX) / q1q2CircleCircleD := by
    field_simp [q1q2CircleCircleD_ne]
    ring
  have hpos :
      0 <
        (2 * Real.sqrt q1q2CircleCircleH2 *
            q1q2CircleCircleDX) / q1q2CircleCircleD := by
    exact div_pos
      (mul_pos (mul_pos (by norm_num) hH) q1q2CircleCircleDX_pos)
      q1q2CircleCircleD_pos
  rw [hdiff_eval] at hdiff
  nlinarith

theorem q1q2CircleRayNearPoint_ne_far :
    q1q2CircleRayNearPoint ≠ q1q2CircleRayFarPoint := by
  intro h
  have hy := congr_fun h 1
  unfold q1q2CircleRayNearPoint q1q2CircleRayFarPoint
    q1q2CircleRayNearTime q1q2CircleRayFarTime at hy
  simp [karlssonOEISQ2, EuclideanLollipop.fromAnchor, angleDirection,
    point2, q2_theta_sin] at hy
  have hsqrt : 0 < Real.sqrt q1q2CircleRayDiscriminant :=
    Real.sqrt_pos.2 q1q2CircleRayDiscriminant_pos
  rcases hy with htime | hcos
  · nlinarith [hsqrt, htime]
  · exact cos_alpha_pos.ne' hcos

theorem q1q2RayCircleNearPoint_ne_far :
    q1q2RayCircleNearPoint ≠ q1q2RayCircleFarPoint := by
  intro h
  have hx := congr_fun h 0
  unfold q1q2RayCircleNearPoint q1q2RayCircleFarPoint
    q1q2RayCircleNearTime q1q2RayCircleFarTime at hx
  simp [karlssonOEISQ1, EuclideanLollipop.fromCenter, angleDirection,
    point2, Real.cos_neg] at hx
  have hsqrt : 0 < Real.sqrt q1q2RayCircleDiscriminant :=
    Real.sqrt_pos.2 q1q2RayCircleDiscriminant_pos
  rcases hx with htime | hcos
  · nlinarith [hsqrt, htime]
  · have hcos_pos : 0 < Real.cos (100 : ℝ)⁻¹ := by
      simpa [theta] using cos_theta_pos
    exact hcos_pos.ne' hcos

private theorem ne_of_left_mem_q1_circle_of_right_not_mem_q1_circle
    {p q : R2}
    (hp : p ∈ circleSet karlssonOEISQ1.center karlssonOEISQ1.radius)
    (hq : q ∉ circleSet karlssonOEISQ1.center karlssonOEISQ1.radius) :
    p ≠ q := by
  intro h
  exact hq (by simpa [h] using hp)

private theorem ne_of_left_mem_q2_circle_of_right_not_mem_q2_circle
    {p q : R2}
    (hp : p ∈ circleSet karlssonOEISQ2.center karlssonOEISQ2.radius)
    (hq : q ∉ circleSet karlssonOEISQ2.center karlssonOEISQ2.radius) :
    p ≠ q := by
  intro h
  exact hq (by simpa [h] using hp)

theorem q1q2CircleCircleUpperPoint_ne_circleRayNear :
    q1q2CircleCircleUpperPoint ≠ q1q2CircleRayNearPoint :=
  ne_of_left_mem_q2_circle_of_right_not_mem_q2_circle
    q1q2CircleCircleUpperPoint_mem_q2_circle
    q1q2CircleRayNearPoint_not_mem_q2_circle

theorem q1q2CircleCircleUpperPoint_ne_circleRayFar :
    q1q2CircleCircleUpperPoint ≠ q1q2CircleRayFarPoint :=
  ne_of_left_mem_q2_circle_of_right_not_mem_q2_circle
    q1q2CircleCircleUpperPoint_mem_q2_circle
    q1q2CircleRayFarPoint_not_mem_q2_circle

theorem q1q2CircleCircleUpperPoint_ne_rayCircleNear :
    q1q2CircleCircleUpperPoint ≠ q1q2RayCircleNearPoint :=
  ne_of_left_mem_q1_circle_of_right_not_mem_q1_circle
    q1q2CircleCircleUpperPoint_mem_q1_circle
    q1q2RayCircleNearPoint_not_mem_q1_circle

theorem q1q2CircleCircleUpperPoint_ne_rayCircleFar :
    q1q2CircleCircleUpperPoint ≠ q1q2RayCircleFarPoint :=
  ne_of_left_mem_q1_circle_of_right_not_mem_q1_circle
    q1q2CircleCircleUpperPoint_mem_q1_circle
    q1q2RayCircleFarPoint_not_mem_q1_circle

theorem q1q2CircleCircleUpperPoint_ne_rayRay :
    q1q2CircleCircleUpperPoint ≠ q1q2RayRayPoint :=
  ne_of_left_mem_q1_circle_of_right_not_mem_q1_circle
    q1q2CircleCircleUpperPoint_mem_q1_circle
    q1q2RayRayPoint_not_mem_q1_circle

theorem q1q2CircleCircleLowerPoint_ne_circleRayNear :
    q1q2CircleCircleLowerPoint ≠ q1q2CircleRayNearPoint :=
  ne_of_left_mem_q2_circle_of_right_not_mem_q2_circle
    q1q2CircleCircleLowerPoint_mem_q2_circle
    q1q2CircleRayNearPoint_not_mem_q2_circle

theorem q1q2CircleCircleLowerPoint_ne_circleRayFar :
    q1q2CircleCircleLowerPoint ≠ q1q2CircleRayFarPoint :=
  ne_of_left_mem_q2_circle_of_right_not_mem_q2_circle
    q1q2CircleCircleLowerPoint_mem_q2_circle
    q1q2CircleRayFarPoint_not_mem_q2_circle

theorem q1q2CircleCircleLowerPoint_ne_rayCircleNear :
    q1q2CircleCircleLowerPoint ≠ q1q2RayCircleNearPoint :=
  ne_of_left_mem_q1_circle_of_right_not_mem_q1_circle
    q1q2CircleCircleLowerPoint_mem_q1_circle
    q1q2RayCircleNearPoint_not_mem_q1_circle

theorem q1q2CircleCircleLowerPoint_ne_rayCircleFar :
    q1q2CircleCircleLowerPoint ≠ q1q2RayCircleFarPoint :=
  ne_of_left_mem_q1_circle_of_right_not_mem_q1_circle
    q1q2CircleCircleLowerPoint_mem_q1_circle
    q1q2RayCircleFarPoint_not_mem_q1_circle

theorem q1q2CircleCircleLowerPoint_ne_rayRay :
    q1q2CircleCircleLowerPoint ≠ q1q2RayRayPoint :=
  ne_of_left_mem_q1_circle_of_right_not_mem_q1_circle
    q1q2CircleCircleLowerPoint_mem_q1_circle
    q1q2RayRayPoint_not_mem_q1_circle

theorem q1q2CircleRayNearPoint_ne_rayCircleNear :
    q1q2CircleRayNearPoint ≠ q1q2RayCircleNearPoint :=
  ne_of_left_mem_q1_circle_of_right_not_mem_q1_circle
    q1q2CircleRayNearPoint_mem_q1_circle
    q1q2RayCircleNearPoint_not_mem_q1_circle

theorem q1q2CircleRayNearPoint_ne_rayCircleFar :
    q1q2CircleRayNearPoint ≠ q1q2RayCircleFarPoint :=
  ne_of_left_mem_q1_circle_of_right_not_mem_q1_circle
    q1q2CircleRayNearPoint_mem_q1_circle
    q1q2RayCircleFarPoint_not_mem_q1_circle

theorem q1q2CircleRayNearPoint_ne_rayRay :
    q1q2CircleRayNearPoint ≠ q1q2RayRayPoint :=
  ne_of_left_mem_q1_circle_of_right_not_mem_q1_circle
    q1q2CircleRayNearPoint_mem_q1_circle
    q1q2RayRayPoint_not_mem_q1_circle

theorem q1q2CircleRayFarPoint_ne_rayCircleNear :
    q1q2CircleRayFarPoint ≠ q1q2RayCircleNearPoint :=
  ne_of_left_mem_q1_circle_of_right_not_mem_q1_circle
    q1q2CircleRayFarPoint_mem_q1_circle
    q1q2RayCircleNearPoint_not_mem_q1_circle

theorem q1q2CircleRayFarPoint_ne_rayCircleFar :
    q1q2CircleRayFarPoint ≠ q1q2RayCircleFarPoint :=
  ne_of_left_mem_q1_circle_of_right_not_mem_q1_circle
    q1q2CircleRayFarPoint_mem_q1_circle
    q1q2RayCircleFarPoint_not_mem_q1_circle

theorem q1q2CircleRayFarPoint_ne_rayRay :
    q1q2CircleRayFarPoint ≠ q1q2RayRayPoint :=
  ne_of_left_mem_q1_circle_of_right_not_mem_q1_circle
    q1q2CircleRayFarPoint_mem_q1_circle
    q1q2RayRayPoint_not_mem_q1_circle

theorem q1q2RayCircleNearPoint_ne_rayRay :
    q1q2RayCircleNearPoint ≠ q1q2RayRayPoint :=
  ne_of_left_mem_q2_circle_of_right_not_mem_q2_circle
    q1q2RayCircleNearPoint_mem_q2_circle
    q1q2RayRayPoint_not_mem_q2_circle

theorem q1q2RayCircleFarPoint_ne_rayRay :
    q1q2RayCircleFarPoint ≠ q1q2RayRayPoint :=
  ne_of_left_mem_q2_circle_of_right_not_mem_q2_circle
    q1q2RayCircleFarPoint_mem_q2_circle
    q1q2RayRayPoint_not_mem_q2_circle

/-- The seven explicit labelled component points for `(Q1,Q2)`. -/
noncomputable def q1q2SevenPointFinset : Finset R2 :=
  {q1q2CircleCircleUpperPoint, q1q2CircleCircleLowerPoint,
    q1q2CircleRayNearPoint, q1q2CircleRayFarPoint,
    q1q2RayCircleNearPoint, q1q2RayCircleFarPoint,
    q1q2RayRayPoint}

theorem q1q2SevenPointFinset_card :
    q1q2SevenPointFinset.card = 7 := by
  classical
  simp [q1q2SevenPointFinset,
    q1q2CircleCircleUpperPoint_ne_lower,
    q1q2CircleCircleUpperPoint_ne_circleRayNear,
    q1q2CircleCircleUpperPoint_ne_circleRayFar,
    q1q2CircleCircleUpperPoint_ne_rayCircleNear,
    q1q2CircleCircleUpperPoint_ne_rayCircleFar,
    q1q2CircleCircleUpperPoint_ne_rayRay,
    q1q2CircleCircleLowerPoint_ne_circleRayNear,
    q1q2CircleCircleLowerPoint_ne_circleRayFar,
    q1q2CircleCircleLowerPoint_ne_rayCircleNear,
    q1q2CircleCircleLowerPoint_ne_rayCircleFar,
    q1q2CircleCircleLowerPoint_ne_rayRay,
    q1q2CircleRayNearPoint_ne_far,
    q1q2CircleRayNearPoint_ne_rayCircleNear,
    q1q2CircleRayNearPoint_ne_rayCircleFar,
    q1q2CircleRayNearPoint_ne_rayRay,
    q1q2CircleRayFarPoint_ne_rayCircleNear,
    q1q2CircleRayFarPoint_ne_rayCircleFar,
    q1q2CircleRayFarPoint_ne_rayRay,
    q1q2RayCircleNearPoint_ne_far,
    q1q2RayCircleNearPoint_ne_rayRay,
    q1q2RayCircleFarPoint_ne_rayRay]

theorem q1q2SevenPointFinset_subset :
    ∀ p ∈ q1q2SevenPointFinset,
      p ∈ karlssonOEISBaseArrangement.pairIntersectionSet
        (1 : Fin 4) (2 : Fin 4) := by
  intro p hp
  simp [q1q2SevenPointFinset] at hp
  rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact q1q2CircleCircleUpperPoint_mem_base_pairIntersectionSet
  · exact q1q2CircleCircleLowerPoint_mem_base_pairIntersectionSet
  · exact q1q2CircleRayNearPoint_mem_base_pairIntersectionSet
  · exact q1q2CircleRayFarPoint_mem_base_pairIntersectionSet
  · exact q1q2RayCircleNearPoint_mem_base_pairIntersectionSet
  · exact q1q2RayCircleFarPoint_mem_base_pairIntersectionSet
  · exact q1q2RayRayPoint_mem_base_pairIntersectionSet

/-- Seven-point lower witness for the exact OEIS base pair `(Q1,Q2)`. -/
noncomputable def q1q2SevenPointSubset :
    OEISSevenPoint.SevenPointSubset (1 : Fin 4) (2 : Fin 4) where
  points := q1q2SevenPointFinset
  card_eq_seven := q1q2SevenPointFinset_card
  points_subset := q1q2SevenPointFinset_subset

/-- Exact pair-coordinate crossing certificate for `(Q1,Q2)`. -/
noncomputable def q1q2PairCoordinateCrossingCertificate :
    KarlssonOEISBasePairCoordinateCrossingCertificate
      (1 : Fin 4) (2 : Fin 4) (by decide) :=
  OEISSevenPoint.pair12Certificate q1q2SevenPointSubset

end

end OEISPair12
end CompleteFormalization
end TheoremOneManuscript
end Lollipop
