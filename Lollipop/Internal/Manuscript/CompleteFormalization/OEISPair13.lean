import Lollipop.Internal.Manuscript.CompleteFormalization.OEISSevenPoint
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.Analysis.Real.Sqrt
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds

/-!
Concrete component witnesses for the OEIS/Karlsson base pair `(Q1,Q3)`.

This file follows the same exact component strategy as `OEISPair12`: two
circle-circle points, two circle-ray points, two ray-circle points, and one
ray-ray point.  The `(Q1,Q3)` ray-ray time along `Q1` is very small, so the
proof uses explicit rational trigonometric bounds.
-/

namespace Lollipop
namespace TheoremOneManuscript
namespace CompleteFormalization

open PrimitiveGeometry

namespace OEISPair13

noncomputable section

open ExplicitInputs
open TheoremOneEndToEnd.PaulsenLinearAlgebra (distSq2 normSq2 dot2)

private abbrev theta : ℝ := (1 : ℝ) / 100
private abbrev beta : ℝ := Real.pi / 30

private theorem theta_pos : 0 < theta := by
  norm_num [theta]

private theorem theta_lt_pi : theta < Real.pi := by
  have htheta : theta < (3 : ℝ) := by
    norm_num [theta]
  exact htheta.trans Real.pi_gt_three

private theorem beta_pos : 0 < beta := by
  dsimp [beta]
  nlinarith [Real.pi_pos]

private theorem beta_lt_pi_div_two : beta < Real.pi / 2 := by
  dsimp [beta]
  nlinarith [Real.pi_pos]

private theorem beta_lt_twenty_one_div_two_hundred :
    beta < (21 : ℝ) / 200 := by
  dsimp [beta]
  nlinarith [Real.pi_lt_d2]

private theorem beta_le_one : beta ≤ 1 := by
  dsimp [beta]
  nlinarith [Real.pi_lt_four]

private theorem sin_theta_pos : 0 < Real.sin theta :=
  Real.sin_pos_of_pos_of_lt_pi theta_pos theta_lt_pi

private theorem sin_theta_lt_theta : Real.sin theta < theta :=
  Real.sin_lt theta_pos

private theorem cos_theta_pos : 0 < Real.cos theta := by
  apply Real.cos_pos_of_mem_Ioo
  constructor <;> nlinarith [theta_pos, Real.pi_gt_three]

private theorem cos_theta_gt_one_half :
    (1 : ℝ) / 2 < Real.cos theta := by
  have hcos := Real.one_sub_sq_div_two_lt_cos
    (x := theta) theta_pos.ne'
  have hhalf : (1 : ℝ) / 2 < 1 - theta ^ 2 / 2 := by
    norm_num [theta]
  exact hhalf.trans hcos

private theorem cos_theta_gt_nine_nine_nine_div_thousand :
    (999 : ℝ) / 1000 < Real.cos theta := by
  have hcos := Real.one_sub_sq_div_two_lt_cos
    (x := theta) theta_pos.ne'
  have hbase : (999 : ℝ) / 1000 < 1 - theta ^ 2 / 2 := by
    norm_num [theta]
  exact hbase.trans hcos

private theorem sin_beta_pos : 0 < Real.sin beta := by
  apply Real.sin_pos_of_pos_of_lt_pi
  · exact beta_pos
  · nlinarith [beta_lt_pi_div_two, Real.pi_pos]

private theorem cos_beta_pos : 0 < Real.cos beta := by
  apply Real.cos_pos_of_mem_Ioo
  constructor
  · nlinarith [beta_pos, Real.pi_pos]
  · exact beta_lt_pi_div_two

private theorem one_half_lt_cos_beta :
    (1 : ℝ) / 2 < Real.cos beta := by
  have h :
      Real.cos (Real.pi / 3) < Real.cos beta :=
    Real.cos_lt_cos_of_nonneg_of_le_pi
      beta_pos.le
      (by nlinarith [Real.pi_pos])
      (by
        dsimp [beta]
        nlinarith [Real.pi_pos])
  simpa [Real.cos_pi_div_three] using h

private theorem sin_beta_lt_twenty_one_div_two_hundred :
    Real.sin beta < (21 : ℝ) / 200 := by
  exact (Real.sin_lt beta_pos).trans beta_lt_twenty_one_div_two_hundred

private theorem thirteen_div_one_twenty_five_lt_sin_beta :
    (13 : ℝ) / 125 < Real.sin beta := by
  have hsin := Real.sin_gt_sub_cube beta_pos beta_le_one
  have hpi_lb : (3.14 : ℝ) < Real.pi := Real.pi_gt_d2
  have hpi_ub : Real.pi < (3.15 : ℝ) := Real.pi_lt_d2
  have hpi_pos : 0 < Real.pi := Real.pi_pos
  have hpi_sq_lt : Real.pi ^ 2 < ((315 : ℝ) / 100) ^ 2 := by
    nlinarith [hpi_ub, hpi_pos]
  have hpi_cube_lt : Real.pi ^ 3 < ((315 : ℝ) / 100) ^ 3 := by
    nlinarith [hpi_ub, hpi_sq_lt, hpi_pos]
  have hsub :
      (13 : ℝ) / 125 < beta - beta ^ 3 / 4 := by
    dsimp [beta]
    nlinarith [hpi_lb, hpi_cube_lt]
  exact hsub.trans hsin

private theorem cos_beta_gt_four_nine_seven_div_five_hundred :
    (497 : ℝ) / 500 < Real.cos beta := by
  have hcos := Real.one_sub_sq_div_two_lt_cos (x := beta) beta_pos.ne'
  have hbeta_sq : beta ^ 2 < ((21 : ℝ) / 200) ^ 2 := by
    nlinarith [beta_pos, beta_lt_twenty_one_div_two_hundred]
  have hbase : (497 : ℝ) / 500 < 1 - beta ^ 2 / 2 := by
    nlinarith [hbeta_sq]
  exact hbase.trans hcos

theorem q3_theta_sin :
    Real.sin karlssonOEISQ3Theta = Real.cos beta := by
  rw [karlssonOEISQ3Theta]
  rw [show Real.pi / 2 + Real.pi / 30 =
    beta + Real.pi / 2 by
      dsimp [beta]
      ring]
  rw [Real.sin_add_pi_div_two]

theorem q3_theta_cos :
    Real.cos karlssonOEISQ3Theta = -Real.sin beta := by
  rw [karlssonOEISQ3Theta]
  rw [show Real.pi / 2 + Real.pi / 30 =
    beta + Real.pi / 2 by
      dsimp [beta]
      ring]
  rw [Real.cos_add_pi_div_two]

private abbrev q1q3AnchorX : ℝ :=
  (45 : ℝ) / 100 + ((55 : ℝ) / 100) * Real.cos theta

private abbrev q1q3AnchorY : ℝ :=
  (4 : ℝ) / 10 - ((55 : ℝ) / 100) * Real.sin theta

private theorem q1_anchor_eq :
    karlssonOEISQ1.anchor =
      point2 q1q3AnchorX q1q3AnchorY := by
  ext i
  fin_cases i
  · simp [karlssonOEISQ1, EuclideanLollipop.fromCenter, angleDirection,
      point2, q1q3AnchorX, theta, Real.cos_neg, Real.sin_neg]
  · simp [karlssonOEISQ1, EuclideanLollipop.fromCenter, angleDirection,
      point2, q1q3AnchorY, theta, Real.cos_neg, Real.sin_neg]
    ring

private abbrev q1q3DeltaX : ℝ :=
  karlssonOEISQ3AnchorX - q1q3AnchorX

private abbrev q1q3DeltaY : ℝ :=
  -((5 : ℝ) / 100) - q1q3AnchorY

private theorem q1q3DeltaX_gt_sixty_one_div_twelve_fifty :
    (61 : ℝ) / 1250 < q1q3DeltaX := by
  unfold q1q3DeltaX q1q3AnchorX
  have hcos_le : Real.cos theta ≤ 1 := Real.cos_le_one theta
  norm_num [karlssonOEISQ3AnchorX] at *
  nlinarith [hcos_le]

private theorem q1q3DeltaX_pos : 0 < q1q3DeltaX := by
  nlinarith [q1q3DeltaX_gt_sixty_one_div_twelve_fifty]

private theorem q1q3DeltaX_lt_one_div_twenty :
    q1q3DeltaX < (1 : ℝ) / 20 := by
  unfold q1q3DeltaX q1q3AnchorX
  norm_num [karlssonOEISQ3AnchorX] at *
  nlinarith [cos_theta_gt_nine_nine_nine_div_thousand]

private theorem q1q3DeltaY_gt_neg_forty_five_div_hundred :
    -((45 : ℝ) / 100) < q1q3DeltaY := by
  unfold q1q3DeltaY q1q3AnchorY
  nlinarith [sin_theta_pos]

private theorem q1q3DeltaY_lt_neg_forty_four_div_hundred :
    q1q3DeltaY < -((44 : ℝ) / 100) := by
  unfold q1q3DeltaY q1q3AnchorY
  have hsmall : Real.sin theta < (1 : ℝ) / 100 := by
    simpa [theta] using sin_theta_lt_theta
  nlinarith [hsmall]

private theorem q1q3_negDeltaY_pos :
    0 < -q1q3DeltaY := by
  nlinarith [q1q3DeltaY_lt_neg_forty_four_div_hundred]

private abbrev q1q3Denom : ℝ :=
  Real.cos theta * Real.cos beta -
    Real.sin theta * Real.sin beta

private theorem q1q3Denom_pos : 0 < q1q3Denom := by
  unfold q1q3Denom
  have hmain :
      (1 : ℝ) / 4 < Real.cos theta * Real.cos beta := by
    nlinarith [cos_theta_gt_one_half,
      cos_beta_gt_four_nine_seven_div_five_hundred]
  have hsmall : Real.sin theta < (1 : ℝ) / 100 := by
    simpa [theta] using sin_theta_lt_theta
  have htail :
      Real.sin theta * Real.sin beta < (1 : ℝ) / 100 := by
    have hsin_le : Real.sin beta ≤ 1 := Real.sin_le_one beta
    nlinarith [sin_theta_pos, hsmall, sin_beta_pos, hsin_le]
  nlinarith [hmain, htail]

private theorem q1q3_timeQ1_numerator_pos :
    0 < q1q3DeltaX * Real.cos beta +
      q1q3DeltaY * Real.sin beta := by
  have hleft :
      ((61 : ℝ) / 1250) * ((497 : ℝ) / 500) <
        q1q3DeltaX * Real.cos beta := by
    nlinarith [q1q3DeltaX_gt_sixty_one_div_twelve_fifty,
      q1q3DeltaX_pos, cos_beta_gt_four_nine_seven_div_five_hundred]
  have hright :
      -(((45 : ℝ) / 100) * ((21 : ℝ) / 200)) <
        q1q3DeltaY * Real.sin beta := by
    nlinarith [q1q3DeltaY_gt_neg_forty_five_div_hundred,
      sin_beta_pos, sin_beta_lt_twenty_one_div_two_hundred]
  nlinarith [hleft, hright]

private theorem q1q3_timeQ3_numerator_pos :
    0 < -q1q3DeltaY * Real.cos theta -
      q1q3DeltaX * Real.sin theta := by
  have hleft :
      (11 : ℝ) / 50 < -q1q3DeltaY * Real.cos theta := by
    have hneg : (44 : ℝ) / 100 < -q1q3DeltaY := by
      nlinarith [q1q3DeltaY_lt_neg_forty_four_div_hundred]
    nlinarith [hneg, cos_theta_gt_one_half]
  have hright :
      q1q3DeltaX * Real.sin theta < (1 : ℝ) / 100 := by
    have hsmall : Real.sin theta < (1 : ℝ) / 100 := by
      simpa [theta] using sin_theta_lt_theta
    nlinarith [q1q3DeltaX_pos, q1q3DeltaX_lt_one_div_twenty,
      sin_theta_pos, hsmall]
  nlinarith [hleft, hright]

/-- Forward time along the `Q1` ray to the `(Q1,Q3)` ray-ray point. -/
noncomputable def q1q3RayRayTimeQ1 : ℝ :=
  (q1q3DeltaX * Real.cos beta +
    q1q3DeltaY * Real.sin beta) / q1q3Denom

/-- Forward time along the `Q3` ray to the same point. -/
noncomputable def q1q3RayRayTimeQ3 : ℝ :=
  (-q1q3DeltaY * Real.cos theta -
    q1q3DeltaX * Real.sin theta) / q1q3Denom

/-- The concrete ray-ray point for the OEIS/Karlsson pair `(Q1,Q3)`. -/
noncomputable def q1q3RayRayPoint : R2 :=
  karlssonOEISQ1.anchor + q1q3RayRayTimeQ1 • karlssonOEISQ1.rayDirection

theorem q1q3RayRayTimeQ1_pos : 0 < q1q3RayRayTimeQ1 := by
  unfold q1q3RayRayTimeQ1
  exact div_pos q1q3_timeQ1_numerator_pos q1q3Denom_pos

theorem q1q3RayRayTimeQ3_pos : 0 < q1q3RayRayTimeQ3 := by
  unfold q1q3RayRayTimeQ3
  exact div_pos q1q3_timeQ3_numerator_pos q1q3Denom_pos

theorem q1q3RayRayPoint_eq_q3_ray_expression :
    q1q3RayRayPoint =
      karlssonOEISQ3.anchor +
        q1q3RayRayTimeQ3 • karlssonOEISQ3.rayDirection := by
  have hden_ne : q1q3Denom ≠ 0 := q1q3Denom_pos.ne'
  ext i
  fin_cases i
  · unfold q1q3RayRayPoint q1q3RayRayTimeQ1 q1q3RayRayTimeQ3
      q1q3DeltaX q1q3DeltaY q1q3AnchorX q1q3AnchorY q1q3Denom
    simp [karlssonOEISQ1, karlssonOEISQ3, EuclideanLollipop.fromCenter,
      EuclideanLollipop.fromAnchor, angleDirection, point2, theta,
      Real.cos_neg, Real.sin_neg, q3_theta_cos, q3_theta_sin]
    field_simp [hden_ne]
    ring
  · unfold q1q3RayRayPoint q1q3RayRayTimeQ1 q1q3RayRayTimeQ3
      q1q3DeltaX q1q3DeltaY q1q3AnchorX q1q3AnchorY q1q3Denom
    simp [karlssonOEISQ1, karlssonOEISQ3, EuclideanLollipop.fromCenter,
      EuclideanLollipop.fromAnchor, angleDirection, point2, theta,
      Real.cos_neg, Real.sin_neg, q3_theta_cos, q3_theta_sin]
    field_simp [hden_ne]
    ring

theorem q1q3RayRayPoint_mem_q1_ray :
    q1q3RayRayPoint ∈
      raySet karlssonOEISQ1.anchor karlssonOEISQ1.rayDirection := by
  exact ⟨q1q3RayRayTimeQ1, q1q3RayRayTimeQ1_pos.le, rfl⟩

theorem q1q3RayRayPoint_mem_q3_ray :
    q1q3RayRayPoint ∈
      raySet karlssonOEISQ3.anchor karlssonOEISQ3.rayDirection := by
  exact ⟨q1q3RayRayTimeQ3, q1q3RayRayTimeQ3_pos.le,
    q1q3RayRayPoint_eq_q3_ray_expression⟩

theorem q1q3RayRayPoint_mem_euclideanRayRaySet :
    toEuclideanR2 q1q3RayRayPoint ∈
      euclideanRayRaySet karlssonOEISQ1 karlssonOEISQ3 :=
  mem_euclideanRayRaySet_of_mem_raySets
    q1q3RayRayPoint_mem_q1_ray q1q3RayRayPoint_mem_q3_ray

theorem q1q3RayRayPoint_mem_base_pairIntersectionSet :
    q1q3RayRayPoint ∈
      karlssonOEISBaseArrangement.pairIntersectionSet
        (1 : Fin 4) (3 : Fin 4) := by
  exact
    OEISSevenPoint.pair_mem_of_euclideanRayRay
      (i := (1 : Fin 4)) (j := (3 : Fin 4))
      (p := q1q3RayRayPoint)
      (by
        simpa [karlssonOEISBaseArrangement] using
          q1q3RayRayPoint_mem_euclideanRayRaySet)

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

private theorem q3_rayDirection_normSq :
    normSq2 karlssonOEISQ3.rayDirection = 1 := by
  simpa [karlssonOEISQ3, EuclideanLollipop.fromAnchor] using
    normSq2_angleDirection karlssonOEISQ3Theta

private abbrev q1q3Q1CenterX : ℝ := (45 : ℝ) / 100
private abbrev q1q3Q1CenterY : ℝ := (4 : ℝ) / 10

private theorem q1q3_q1_center_eq :
    karlssonOEISQ1.center =
      point2 q1q3Q1CenterX q1q3Q1CenterY := by
  ext i
  fin_cases i <;>
    simp [karlssonOEISQ1, EuclideanLollipop.fromCenter, point2,
      q1q3Q1CenterX, q1q3Q1CenterY]

private abbrev q1q3Q3CenterX : ℝ :=
  karlssonOEISQ3AnchorX + 100 * Real.sin beta

private abbrev q1q3Q3CenterY : ℝ :=
  -((5 : ℝ) / 100) - 100 * Real.cos beta

private theorem q1q3_q3_center_eq :
    karlssonOEISQ3.center =
      point2 q1q3Q3CenterX q1q3Q3CenterY := by
  ext i
  fin_cases i <;>
    simp [karlssonOEISQ3, EuclideanLollipop.fromAnchor, angleDirection,
      point2, q1q3Q3CenterX, q1q3Q3CenterY, q3_theta_cos,
      q3_theta_sin]

private abbrev q1q3AnchorToQ1CenterX : ℝ :=
  karlssonOEISQ3AnchorX - q1q3Q1CenterX

private theorem q1q3AnchorToQ1CenterX_gt :
    (1497 : ℝ) / 2500 < q1q3AnchorToQ1CenterX := by
  norm_num [q1q3AnchorToQ1CenterX, q1q3Q1CenterX,
    karlssonOEISQ3AnchorX]

private theorem q1q3AnchorToQ1CenterX_lt :
    q1q3AnchorToQ1CenterX < (599 : ℝ) / 1000 := by
  norm_num [q1q3AnchorToQ1CenterX, q1q3Q1CenterX,
    karlssonOEISQ3AnchorX]

/-- Positive dot coefficient in the quadratic for
`circle(Q1) ∩ ray(Q3)`. -/
private abbrev q1q3CircleRayDot : ℝ :=
  -dot2 (karlssonOEISQ3.anchor - karlssonOEISQ1.center)
    karlssonOEISQ3.rayDirection

/-- Constant term in the quadratic for `circle(Q1) ∩ ray(Q3)`. -/
private abbrev q1q3CircleRayConstant : ℝ :=
  distSq2 karlssonOEISQ3.anchor karlssonOEISQ1.center -
    karlssonOEISQ1.radius ^ 2

/-- Discriminant for `circle(Q1) ∩ ray(Q3)`. -/
private abbrev q1q3CircleRayDiscriminant : ℝ :=
  q1q3CircleRayDot ^ 2 - q1q3CircleRayConstant

private theorem q1q3CircleRayDot_expanded :
    q1q3CircleRayDot =
      q1q3AnchorToQ1CenterX * Real.sin beta +
        ((45 : ℝ) / 100) * Real.cos beta := by
  unfold q1q3CircleRayDot q1q3AnchorToQ1CenterX dot2
  simp [karlssonOEISQ1, karlssonOEISQ3, EuclideanLollipop.fromCenter,
    EuclideanLollipop.fromAnchor, angleDirection, point2,
    q3_theta_cos, q3_theta_sin]
  ring

private theorem q1q3CircleRayConstant_expanded :
    q1q3CircleRayConstant =
      q1q3AnchorToQ1CenterX ^ 2 - (1 : ℝ) / 10 := by
  unfold q1q3CircleRayConstant q1q3AnchorToQ1CenterX
    distSq2 normSq2 dot2
  simp [karlssonOEISQ1, karlssonOEISQ3, EuclideanLollipop.fromCenter,
    EuclideanLollipop.fromAnchor, angleDirection, point2]
  ring

private theorem q1q3CircleRayDot_gt :
    (2547 : ℝ) / 5000 < q1q3CircleRayDot := by
  rw [q1q3CircleRayDot_expanded]
  nlinarith [q1q3AnchorToQ1CenterX_gt,
    thirteen_div_one_twenty_five_lt_sin_beta,
    cos_beta_gt_four_nine_seven_div_five_hundred]

private theorem q1q3CircleRayDot_pos :
    0 < q1q3CircleRayDot := by
  nlinarith [q1q3CircleRayDot_gt]

private theorem q1q3CircleRayConstant_pos :
    0 < q1q3CircleRayConstant := by
  rw [q1q3CircleRayConstant_expanded]
  nlinarith [q1q3AnchorToQ1CenterX_gt]

private theorem q1q3CircleRayConstant_lt :
    q1q3CircleRayConstant < (2589 : ℝ) / 10000 := by
  rw [q1q3CircleRayConstant_expanded]
  have hsq : q1q3AnchorToQ1CenterX ^ 2 < ((599 : ℝ) / 1000) ^ 2 := by
    nlinarith [q1q3AnchorToQ1CenterX_gt,
      q1q3AnchorToQ1CenterX_lt]
  nlinarith [hsq]

private theorem q1q3CircleRayDiscriminant_pos :
    0 < q1q3CircleRayDiscriminant := by
  unfold q1q3CircleRayDiscriminant
  nlinarith [q1q3CircleRayDot_gt, q1q3CircleRayConstant_lt]

private theorem q1q3CircleRayDiscriminant_nonneg :
    0 ≤ q1q3CircleRayDiscriminant :=
  q1q3CircleRayDiscriminant_pos.le

private theorem q1q3CircleRay_sqrt_le_dot :
    Real.sqrt q1q3CircleRayDiscriminant ≤ q1q3CircleRayDot := by
  rw [Real.sqrt_le_iff]
  exact ⟨q1q3CircleRayDot_pos.le, by
    unfold q1q3CircleRayDiscriminant
    nlinarith [q1q3CircleRayConstant_pos]⟩

noncomputable def q1q3CircleRayNearTime : ℝ :=
  q1q3CircleRayDot - Real.sqrt q1q3CircleRayDiscriminant

noncomputable def q1q3CircleRayFarTime : ℝ :=
  q1q3CircleRayDot + Real.sqrt q1q3CircleRayDiscriminant

noncomputable def q1q3CircleRayNearPoint : R2 :=
  karlssonOEISQ3.anchor +
    q1q3CircleRayNearTime • karlssonOEISQ3.rayDirection

noncomputable def q1q3CircleRayFarPoint : R2 :=
  karlssonOEISQ3.anchor +
    q1q3CircleRayFarTime • karlssonOEISQ3.rayDirection

theorem q1q3CircleRayNearTime_nonneg :
    0 ≤ q1q3CircleRayNearTime := by
  unfold q1q3CircleRayNearTime
  nlinarith [q1q3CircleRay_sqrt_le_dot]

theorem q1q3CircleRayFarTime_nonneg :
    0 ≤ q1q3CircleRayFarTime := by
  unfold q1q3CircleRayFarTime
  nlinarith [q1q3CircleRayDot_pos,
    Real.sqrt_nonneg q1q3CircleRayDiscriminant]

private theorem q1q3CircleRayNearTime_quadratic :
    q1q3CircleRayNearTime ^ 2 -
        2 * q1q3CircleRayDot * q1q3CircleRayNearTime +
        q1q3CircleRayConstant = 0 := by
  unfold q1q3CircleRayNearTime q1q3CircleRayDiscriminant
  have hsqrt_sq :
      (Real.sqrt
          (q1q3CircleRayDot ^ 2 - q1q3CircleRayConstant)) ^ 2 =
        q1q3CircleRayDot ^ 2 - q1q3CircleRayConstant := by
    rw [Real.sq_sqrt]
    simpa [q1q3CircleRayDiscriminant] using
      q1q3CircleRayDiscriminant_nonneg
  nlinarith [hsqrt_sq]

private theorem q1q3CircleRayFarTime_quadratic :
    q1q3CircleRayFarTime ^ 2 -
        2 * q1q3CircleRayDot * q1q3CircleRayFarTime +
        q1q3CircleRayConstant = 0 := by
  unfold q1q3CircleRayFarTime q1q3CircleRayDiscriminant
  have hsqrt_sq :
      (Real.sqrt
          (q1q3CircleRayDot ^ 2 - q1q3CircleRayConstant)) ^ 2 =
        q1q3CircleRayDot ^ 2 - q1q3CircleRayConstant := by
    rw [Real.sq_sqrt]
    simpa [q1q3CircleRayDiscriminant] using
      q1q3CircleRayDiscriminant_nonneg
  nlinarith [hsqrt_sq]

theorem q1q3CircleRayNearPoint_mem_q1_circle :
    q1q3CircleRayNearPoint ∈
      circleSet karlssonOEISQ1.center karlssonOEISQ1.radius := by
  unfold q1q3CircleRayNearPoint
  exact
    ray_point_mem_circle_of_quadratic
      (anchor := karlssonOEISQ3.anchor)
      (center := karlssonOEISQ1.center)
      (direction := karlssonOEISQ3.rayDirection)
      (radius := karlssonOEISQ1.radius)
      (dot := q1q3CircleRayDot)
      (constant := q1q3CircleRayConstant)
      rfl rfl q3_rayDirection_normSq
      q1q3CircleRayNearTime_quadratic

theorem q1q3CircleRayFarPoint_mem_q1_circle :
    q1q3CircleRayFarPoint ∈
      circleSet karlssonOEISQ1.center karlssonOEISQ1.radius := by
  unfold q1q3CircleRayFarPoint
  exact
    ray_point_mem_circle_of_quadratic
      (anchor := karlssonOEISQ3.anchor)
      (center := karlssonOEISQ1.center)
      (direction := karlssonOEISQ3.rayDirection)
      (radius := karlssonOEISQ1.radius)
      (dot := q1q3CircleRayDot)
      (constant := q1q3CircleRayConstant)
      rfl rfl q3_rayDirection_normSq
      q1q3CircleRayFarTime_quadratic

theorem q1q3CircleRayNearPoint_mem_q3_ray :
    q1q3CircleRayNearPoint ∈
      raySet karlssonOEISQ3.anchor karlssonOEISQ3.rayDirection := by
  exact ⟨q1q3CircleRayNearTime, q1q3CircleRayNearTime_nonneg, rfl⟩

theorem q1q3CircleRayFarPoint_mem_q3_ray :
    q1q3CircleRayFarPoint ∈
      raySet karlssonOEISQ3.anchor karlssonOEISQ3.rayDirection := by
  exact ⟨q1q3CircleRayFarTime, q1q3CircleRayFarTime_nonneg, rfl⟩

theorem q1q3CircleRayNearPoint_mem_euclideanCircleRaySet :
    toEuclideanR2 q1q3CircleRayNearPoint ∈
      euclideanCircleRaySet karlssonOEISQ1 karlssonOEISQ3 :=
  mem_euclideanCircleRaySet_of_mem_circleSet_of_mem_raySet
    q1q3CircleRayNearPoint_mem_q1_circle
    q1q3CircleRayNearPoint_mem_q3_ray

theorem q1q3CircleRayFarPoint_mem_euclideanCircleRaySet :
    toEuclideanR2 q1q3CircleRayFarPoint ∈
      euclideanCircleRaySet karlssonOEISQ1 karlssonOEISQ3 :=
  mem_euclideanCircleRaySet_of_mem_circleSet_of_mem_raySet
    q1q3CircleRayFarPoint_mem_q1_circle
    q1q3CircleRayFarPoint_mem_q3_ray

theorem q1q3CircleRayNearPoint_mem_base_pairIntersectionSet :
    q1q3CircleRayNearPoint ∈
      karlssonOEISBaseArrangement.pairIntersectionSet
        (1 : Fin 4) (3 : Fin 4) := by
  exact
    OEISSevenPoint.pair_mem_of_euclideanCircleRay
      (i := (1 : Fin 4)) (j := (3 : Fin 4))
      (p := q1q3CircleRayNearPoint)
      (by
        simpa [karlssonOEISBaseArrangement] using
          q1q3CircleRayNearPoint_mem_euclideanCircleRaySet)

theorem q1q3CircleRayFarPoint_mem_base_pairIntersectionSet :
    q1q3CircleRayFarPoint ∈
      karlssonOEISBaseArrangement.pairIntersectionSet
        (1 : Fin 4) (3 : Fin 4) := by
  exact
    OEISSevenPoint.pair_mem_of_euclideanCircleRay
      (i := (1 : Fin 4)) (j := (3 : Fin 4))
      (p := q1q3CircleRayFarPoint)
      (by
        simpa [karlssonOEISBaseArrangement] using
          q1q3CircleRayFarPoint_mem_euclideanCircleRaySet)

/-- Positive dot coefficient in the quadratic for
`ray(Q1) ∩ circle(Q3)`. -/
private abbrev q1q3RayCircleDot : ℝ :=
  -dot2 (karlssonOEISQ1.anchor - karlssonOEISQ3.center)
    karlssonOEISQ1.rayDirection

/-- Constant term in the quadratic for `ray(Q1) ∩ circle(Q3)`. -/
private abbrev q1q3RayCircleConstant : ℝ :=
  distSq2 karlssonOEISQ1.anchor karlssonOEISQ3.center -
    karlssonOEISQ3.radius ^ 2

/-- Discriminant for `ray(Q1) ∩ circle(Q3)`. -/
private abbrev q1q3RayCircleDiscriminant : ℝ :=
  q1q3RayCircleDot ^ 2 - q1q3RayCircleConstant

private theorem q1q3RayCircleDot_expanded :
    q1q3RayCircleDot =
      (q1q3DeltaX + (100 : ℝ) * Real.sin beta) * Real.cos theta +
        (-q1q3DeltaY + (100 : ℝ) * Real.cos beta) *
          Real.sin theta := by
  unfold q1q3RayCircleDot q1q3DeltaX q1q3DeltaY q1q3AnchorX
    q1q3AnchorY dot2
  simp [karlssonOEISQ1, karlssonOEISQ3, EuclideanLollipop.fromCenter,
    EuclideanLollipop.fromAnchor, angleDirection, point2, theta,
    Real.cos_neg, Real.sin_neg, q3_theta_cos, q3_theta_sin]
  ring

private theorem q1q3RayCircleConstant_expanded :
    q1q3RayCircleConstant =
      q1q3DeltaX ^ 2 + q1q3DeltaY ^ 2 +
        200 * q1q3DeltaX * Real.sin beta -
        200 * q1q3DeltaY * Real.cos beta := by
  unfold q1q3RayCircleConstant q1q3DeltaX q1q3DeltaY
    q1q3AnchorX q1q3AnchorY distSq2 normSq2 dot2
  simp [karlssonOEISQ1, karlssonOEISQ3, EuclideanLollipop.fromCenter,
    EuclideanLollipop.fromAnchor, angleDirection, point2, theta,
    Real.cos_neg, Real.sin_neg, q3_theta_cos, q3_theta_sin]
  ring_nf
  have htrig :
      Real.sin (Real.pi * (1 / 30 : ℝ)) ^ 2 +
          Real.cos (Real.pi * (1 / 30 : ℝ)) ^ 2 = 1 :=
    Real.sin_sq_add_cos_sq (Real.pi * (1 / 30 : ℝ))
  nlinarith [htrig]

private theorem q1q3RayCircleDot_gt_ten :
    (10 : ℝ) < q1q3RayCircleDot := by
  rw [q1q3RayCircleDot_expanded]
  have hbase :
      (52 : ℝ) / 5 <
        q1q3DeltaX + (100 : ℝ) * Real.sin beta := by
    nlinarith [q1q3DeltaX_pos, thirteen_div_one_twenty_five_lt_sin_beta]
  have hleft :
      (10 : ℝ) <
        (q1q3DeltaX + (100 : ℝ) * Real.sin beta) *
          Real.cos theta := by
    nlinarith [hbase, cos_theta_gt_nine_nine_nine_div_thousand]
  have htail :
      0 <
        (-q1q3DeltaY + (100 : ℝ) * Real.cos beta) *
          Real.sin theta := by
    nlinarith [q1q3_negDeltaY_pos, cos_beta_pos, sin_theta_pos]
  nlinarith [hleft, htail]

private theorem q1q3RayCircleDot_pos :
    0 < q1q3RayCircleDot := by
  nlinarith [q1q3RayCircleDot_gt_ten]

private theorem q1q3RayCircleConstant_pos :
    0 < q1q3RayCircleConstant := by
  rw [q1q3RayCircleConstant_expanded]
  have hx :
      0 < 200 * q1q3DeltaX * Real.sin beta := by
    nlinarith [q1q3DeltaX_pos, sin_beta_pos]
  have hy :
      0 < -(200 * q1q3DeltaY * Real.cos beta) := by
    nlinarith [q1q3_negDeltaY_pos, cos_beta_pos]
  nlinarith [sq_nonneg q1q3DeltaX, sq_nonneg q1q3DeltaY, hx, hy]

private theorem q1q3RayCircleConstant_lt_hundred :
    q1q3RayCircleConstant < (100 : ℝ) := by
  rw [q1q3RayCircleConstant_expanded]
  have hx_sq : q1q3DeltaX ^ 2 < 1 := by
    nlinarith [q1q3DeltaX_pos, q1q3DeltaX_lt_one_div_twenty]
  have hy_sq : q1q3DeltaY ^ 2 < 1 := by
    nlinarith [q1q3DeltaY_gt_neg_forty_five_div_hundred,
      q1q3DeltaY_lt_neg_forty_four_div_hundred]
  have hxsin :
      q1q3DeltaX * Real.sin beta < (21 : ℝ) / 4000 := by
    nlinarith [q1q3DeltaX_pos, q1q3DeltaX_lt_one_div_twenty,
      sin_beta_pos, sin_beta_lt_twenty_one_div_two_hundred]
  have hycos :
      -q1q3DeltaY * Real.cos beta < (45 : ℝ) / 100 := by
    have hcos_le : Real.cos beta ≤ 1 := Real.cos_le_one beta
    nlinarith [q1q3DeltaY_gt_neg_forty_five_div_hundred,
      q1q3_negDeltaY_pos, cos_beta_pos, hcos_le]
  nlinarith [hx_sq, hy_sq, hxsin, hycos]

private theorem q1q3RayCircleDiscriminant_pos :
    0 < q1q3RayCircleDiscriminant := by
  unfold q1q3RayCircleDiscriminant
  nlinarith [q1q3RayCircleDot_gt_ten,
    q1q3RayCircleConstant_lt_hundred]

private theorem q1q3RayCircleDiscriminant_nonneg :
    0 ≤ q1q3RayCircleDiscriminant :=
  q1q3RayCircleDiscriminant_pos.le

private theorem q1q3RayCircle_sqrt_le_dot :
    Real.sqrt q1q3RayCircleDiscriminant ≤ q1q3RayCircleDot := by
  rw [Real.sqrt_le_iff]
  exact ⟨q1q3RayCircleDot_pos.le, by
    unfold q1q3RayCircleDiscriminant
    nlinarith [q1q3RayCircleConstant_pos]⟩

noncomputable def q1q3RayCircleNearTime : ℝ :=
  q1q3RayCircleDot - Real.sqrt q1q3RayCircleDiscriminant

noncomputable def q1q3RayCircleFarTime : ℝ :=
  q1q3RayCircleDot + Real.sqrt q1q3RayCircleDiscriminant

noncomputable def q1q3RayCircleNearPoint : R2 :=
  karlssonOEISQ1.anchor +
    q1q3RayCircleNearTime • karlssonOEISQ1.rayDirection

noncomputable def q1q3RayCircleFarPoint : R2 :=
  karlssonOEISQ1.anchor +
    q1q3RayCircleFarTime • karlssonOEISQ1.rayDirection

theorem q1q3RayCircleNearTime_nonneg :
    0 ≤ q1q3RayCircleNearTime := by
  unfold q1q3RayCircleNearTime
  nlinarith [q1q3RayCircle_sqrt_le_dot]

theorem q1q3RayCircleFarTime_nonneg :
    0 ≤ q1q3RayCircleFarTime := by
  unfold q1q3RayCircleFarTime
  nlinarith [q1q3RayCircleDot_pos,
    Real.sqrt_nonneg q1q3RayCircleDiscriminant]

private theorem q1q3RayCircleNearTime_quadratic :
    q1q3RayCircleNearTime ^ 2 -
        2 * q1q3RayCircleDot * q1q3RayCircleNearTime +
        q1q3RayCircleConstant = 0 := by
  unfold q1q3RayCircleNearTime q1q3RayCircleDiscriminant
  have hsqrt_sq :
      (Real.sqrt
          (q1q3RayCircleDot ^ 2 - q1q3RayCircleConstant)) ^ 2 =
        q1q3RayCircleDot ^ 2 - q1q3RayCircleConstant := by
    rw [Real.sq_sqrt]
    simpa [q1q3RayCircleDiscriminant] using
      q1q3RayCircleDiscriminant_nonneg
  nlinarith [hsqrt_sq]

private theorem q1q3RayCircleFarTime_quadratic :
    q1q3RayCircleFarTime ^ 2 -
        2 * q1q3RayCircleDot * q1q3RayCircleFarTime +
        q1q3RayCircleConstant = 0 := by
  unfold q1q3RayCircleFarTime q1q3RayCircleDiscriminant
  have hsqrt_sq :
      (Real.sqrt
          (q1q3RayCircleDot ^ 2 - q1q3RayCircleConstant)) ^ 2 =
        q1q3RayCircleDot ^ 2 - q1q3RayCircleConstant := by
    rw [Real.sq_sqrt]
    simpa [q1q3RayCircleDiscriminant] using
      q1q3RayCircleDiscriminant_nonneg
  nlinarith [hsqrt_sq]

theorem q1q3RayCircleNearPoint_mem_q1_ray :
    q1q3RayCircleNearPoint ∈
      raySet karlssonOEISQ1.anchor karlssonOEISQ1.rayDirection := by
  exact ⟨q1q3RayCircleNearTime, q1q3RayCircleNearTime_nonneg, rfl⟩

theorem q1q3RayCircleFarPoint_mem_q1_ray :
    q1q3RayCircleFarPoint ∈
      raySet karlssonOEISQ1.anchor karlssonOEISQ1.rayDirection := by
  exact ⟨q1q3RayCircleFarTime, q1q3RayCircleFarTime_nonneg, rfl⟩

theorem q1q3RayCircleNearPoint_mem_q3_circle :
    q1q3RayCircleNearPoint ∈
      circleSet karlssonOEISQ3.center karlssonOEISQ3.radius := by
  unfold q1q3RayCircleNearPoint
  exact
    ray_point_mem_circle_of_quadratic
      (anchor := karlssonOEISQ1.anchor)
      (center := karlssonOEISQ3.center)
      (direction := karlssonOEISQ1.rayDirection)
      (radius := karlssonOEISQ3.radius)
      (dot := q1q3RayCircleDot)
      (constant := q1q3RayCircleConstant)
      rfl rfl q1_rayDirection_normSq
      q1q3RayCircleNearTime_quadratic

theorem q1q3RayCircleFarPoint_mem_q3_circle :
    q1q3RayCircleFarPoint ∈
      circleSet karlssonOEISQ3.center karlssonOEISQ3.radius := by
  unfold q1q3RayCircleFarPoint
  exact
    ray_point_mem_circle_of_quadratic
      (anchor := karlssonOEISQ1.anchor)
      (center := karlssonOEISQ3.center)
      (direction := karlssonOEISQ1.rayDirection)
      (radius := karlssonOEISQ3.radius)
      (dot := q1q3RayCircleDot)
      (constant := q1q3RayCircleConstant)
      rfl rfl q1_rayDirection_normSq
      q1q3RayCircleFarTime_quadratic

theorem q1q3RayCircleNearPoint_mem_euclideanRayCircleSet :
    toEuclideanR2 q1q3RayCircleNearPoint ∈
      euclideanRayCircleSet karlssonOEISQ1 karlssonOEISQ3 :=
  mem_euclideanRayCircleSet_of_mem_raySet_of_mem_circleSet
    q1q3RayCircleNearPoint_mem_q1_ray
    q1q3RayCircleNearPoint_mem_q3_circle

theorem q1q3RayCircleFarPoint_mem_euclideanRayCircleSet :
    toEuclideanR2 q1q3RayCircleFarPoint ∈
      euclideanRayCircleSet karlssonOEISQ1 karlssonOEISQ3 :=
  mem_euclideanRayCircleSet_of_mem_raySet_of_mem_circleSet
    q1q3RayCircleFarPoint_mem_q1_ray
    q1q3RayCircleFarPoint_mem_q3_circle

theorem q1q3RayCircleNearPoint_mem_base_pairIntersectionSet :
    q1q3RayCircleNearPoint ∈
      karlssonOEISBaseArrangement.pairIntersectionSet
        (1 : Fin 4) (3 : Fin 4) := by
  exact
    OEISSevenPoint.pair_mem_of_euclideanRayCircle
      (i := (1 : Fin 4)) (j := (3 : Fin 4))
      (p := q1q3RayCircleNearPoint)
      (by
        simpa [karlssonOEISBaseArrangement] using
          q1q3RayCircleNearPoint_mem_euclideanRayCircleSet)

theorem q1q3RayCircleFarPoint_mem_base_pairIntersectionSet :
    q1q3RayCircleFarPoint ∈
      karlssonOEISBaseArrangement.pairIntersectionSet
        (1 : Fin 4) (3 : Fin 4) := by
  exact
    OEISSevenPoint.pair_mem_of_euclideanRayCircle
      (i := (1 : Fin 4)) (j := (3 : Fin 4))
      (p := q1q3RayCircleFarPoint)
      (by
        simpa [karlssonOEISBaseArrangement] using
          q1q3RayCircleFarPoint_mem_euclideanRayCircleSet)

private abbrev q1q3CircleCircleDX : ℝ :=
  q1q3Q3CenterX - q1q3Q1CenterX

private abbrev q1q3CircleCircleDY : ℝ :=
  q1q3Q3CenterY - q1q3Q1CenterY

private abbrev q1q3CircleCircleD : ℝ :=
  q1q3CircleCircleDX ^ 2 + q1q3CircleCircleDY ^ 2

private abbrev q1q3CircleCircleA : ℝ :=
  (q1q3CircleCircleD + ((11 : ℝ) / 20) ^ 2 - (100 : ℝ) ^ 2) / 2

private abbrev q1q3CircleCircleH2 : ℝ :=
  ((11 : ℝ) / 20) ^ 2 * q1q3CircleCircleD -
    q1q3CircleCircleA ^ 2

private theorem q1q3CircleCircleD_expanded :
    q1q3CircleCircleD =
      (10000 : ℝ) +
        200 * q1q3AnchorToQ1CenterX * Real.sin beta +
        90 * Real.cos beta +
        q1q3AnchorToQ1CenterX ^ 2 + (81 : ℝ) / 400 := by
  unfold q1q3CircleCircleD q1q3CircleCircleDX q1q3CircleCircleDY
    q1q3Q3CenterX q1q3Q3CenterY q1q3Q1CenterX q1q3Q1CenterY
    q1q3AnchorToQ1CenterX
  ring_nf
  have htrig :
      Real.sin (Real.pi * (1 / 30 : ℝ)) ^ 2 +
          Real.cos (Real.pi * (1 / 30 : ℝ)) ^ 2 = 1 :=
    Real.sin_sq_add_cos_sq (Real.pi * (1 / 30 : ℝ))
  nlinarith [htrig]

private theorem q1q3CircleCircleD_gt_radius_diff_sq :
    ((1989 : ℝ) / 20) ^ 2 < q1q3CircleCircleD := by
  rw [q1q3CircleCircleD_expanded]
  have hprod :
      0 < 200 * q1q3AnchorToQ1CenterX * Real.sin beta := by
    nlinarith [q1q3AnchorToQ1CenterX_gt, sin_beta_pos]
  nlinarith [hprod, cos_beta_pos, sq_nonneg q1q3AnchorToQ1CenterX]

private theorem q1q3CircleCircleD_lt_radius_sum_sq :
    q1q3CircleCircleD < ((2011 : ℝ) / 20) ^ 2 := by
  rw [q1q3CircleCircleD_expanded]
  have hcos_le : Real.cos beta ≤ 1 := Real.cos_le_one beta
  have hsq : q1q3AnchorToQ1CenterX ^ 2 < ((3 : ℝ) / 5) ^ 2 := by
    nlinarith [q1q3AnchorToQ1CenterX_gt, q1q3AnchorToQ1CenterX_lt]
  nlinarith [q1q3AnchorToQ1CenterX_gt, q1q3AnchorToQ1CenterX_lt,
    sin_beta_pos, sin_beta_lt_twenty_one_div_two_hundred, hcos_le, hsq]

/-- The private center-distance abbreviation is exactly the squared distance
between the `Q1` and `Q3` circle centers. -/
theorem q1q3CircleCircleD_eq_distSq2_centers :
    q1q3CircleCircleD =
      distSq2 karlssonOEISQ1.center karlssonOEISQ3.center := by
  rw [q1q3_q1_center_eq, q1q3_q3_center_eq]
  simp [q1q3CircleCircleD, q1q3CircleCircleDX, q1q3CircleCircleDY,
    q1q3Q1CenterX, q1q3Q1CenterY, q1q3Q3CenterX, q1q3Q3CenterY,
    distSq2, normSq2, dot2, point2]
  ring

/-- The `Q1,Q3` circle pair satisfies Paulsen's strict obtuse-intersection
distance condition, hence is not intriguing. -/
theorem q1q3_circleObtuseCondition :
    TheoremOneEndToEnd.PaulsenLinearAlgebra.circleObtuseCondition
      karlssonOEISQ1.radius karlssonOEISQ3.radius
      karlssonOEISQ1.center karlssonOEISQ3.center := by
  unfold TheoremOneEndToEnd.PaulsenLinearAlgebra.circleObtuseCondition
  constructor
  · rw [← q1q3CircleCircleD_eq_distSq2_centers]
    rw [q1q3CircleCircleD_expanded]
    have hrad :
        karlssonOEISQ1.radius ^ 2 + karlssonOEISQ3.radius ^ 2 =
          (10000 : ℝ) + (121 : ℝ) / 400 := by
      norm_num [karlssonOEISQ1, karlssonOEISQ3,
        EuclideanLollipop.fromCenter, EuclideanLollipop.fromAnchor]
    have hprod :
        0 < 200 * q1q3AnchorToQ1CenterX * Real.sin beta := by
      nlinarith [q1q3AnchorToQ1CenterX_gt, sin_beta_pos]
    rw [hrad]
    nlinarith [hprod, one_half_lt_cos_beta,
      sq_nonneg q1q3AnchorToQ1CenterX]
  · rw [← q1q3CircleCircleD_eq_distSq2_centers]
    have hsum :
        (karlssonOEISQ1.radius + karlssonOEISQ3.radius) ^ 2 =
          ((2011 : ℝ) / 20) ^ 2 := by
      norm_num [karlssonOEISQ1, karlssonOEISQ3,
        EuclideanLollipop.fromCenter, EuclideanLollipop.fromAnchor]
    rw [hsum]
    exact q1q3CircleCircleD_lt_radius_sum_sq

/-- Pair-level form: `(Q1,Q3)` is not intriguing. -/
theorem q1q3_not_circleIntriguingPair :
    ¬ TheoremOneEndToEnd.PaulsenLinearAlgebra.circleIntriguingPair
      karlssonOEISQ1.radius karlssonOEISQ3.radius
      karlssonOEISQ1.center karlssonOEISQ3.center := by
  classical
  exact not_not.mpr q1q3_circleObtuseCondition

private theorem q1q3CircleCircleD_pos :
    0 < q1q3CircleCircleD := by
  nlinarith [q1q3CircleCircleD_gt_radius_diff_sq]

private theorem q1q3CircleCircleD_ne :
    q1q3CircleCircleD ≠ 0 :=
  q1q3CircleCircleD_pos.ne'

private theorem q1q3CircleCircleH2_pos :
    0 < q1q3CircleCircleH2 := by
  unfold q1q3CircleCircleH2 q1q3CircleCircleA
  have hprod :
      0 <
        (((2011 : ℝ) / 20) ^ 2 - q1q3CircleCircleD) *
          (q1q3CircleCircleD - ((1989 : ℝ) / 20) ^ 2) :=
    mul_pos (sub_pos.2 q1q3CircleCircleD_lt_radius_sum_sq)
      (sub_pos.2 q1q3CircleCircleD_gt_radius_diff_sq)
  nlinarith [hprod]

private theorem q1q3CircleCircleH2_nonneg :
    0 ≤ q1q3CircleCircleH2 :=
  q1q3CircleCircleH2_pos.le

noncomputable def q1q3CircleCircleUpperPoint : R2 :=
  point2
    (q1q3Q1CenterX +
      (q1q3CircleCircleA * q1q3CircleCircleDX -
        Real.sqrt q1q3CircleCircleH2 * q1q3CircleCircleDY) /
        q1q3CircleCircleD)
    (q1q3Q1CenterY +
      (q1q3CircleCircleA * q1q3CircleCircleDY +
        Real.sqrt q1q3CircleCircleH2 * q1q3CircleCircleDX) /
        q1q3CircleCircleD)

noncomputable def q1q3CircleCircleLowerPoint : R2 :=
  point2
    (q1q3Q1CenterX +
      (q1q3CircleCircleA * q1q3CircleCircleDX +
        Real.sqrt q1q3CircleCircleH2 * q1q3CircleCircleDY) /
        q1q3CircleCircleD)
    (q1q3Q1CenterY +
      (q1q3CircleCircleA * q1q3CircleCircleDY -
        Real.sqrt q1q3CircleCircleH2 * q1q3CircleCircleDX) /
        q1q3CircleCircleD)

private theorem q1q3CircleCircle_sqrt_sq :
    (Real.sqrt q1q3CircleCircleH2) ^ 2 =
      q1q3CircleCircleH2 :=
  Real.sq_sqrt q1q3CircleCircleH2_nonneg

private theorem q1q3CircleCircle_A_sq_add_H_sq_q1 :
    q1q3CircleCircleA ^ 2 +
        (Real.sqrt q1q3CircleCircleH2) ^ 2 =
      ((11 : ℝ) / 20) ^ 2 * q1q3CircleCircleD := by
  rw [q1q3CircleCircle_sqrt_sq]
  unfold q1q3CircleCircleH2
  ring

private theorem q1q3CircleCircle_A_sub_D_sq_add_H_sq_q3 :
    (q1q3CircleCircleA - q1q3CircleCircleD) ^ 2 +
        (Real.sqrt q1q3CircleCircleH2) ^ 2 =
      (100 : ℝ) ^ 2 * q1q3CircleCircleD := by
  rw [q1q3CircleCircle_sqrt_sq]
  unfold q1q3CircleCircleH2 q1q3CircleCircleA
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

private theorem q1q3CircleCircleUpper_q1_coordinate :
    ((q1q3CircleCircleA * q1q3CircleCircleDX -
          Real.sqrt q1q3CircleCircleH2 * q1q3CircleCircleDY) /
        q1q3CircleCircleD) *
        ((q1q3CircleCircleA * q1q3CircleCircleDX -
            Real.sqrt q1q3CircleCircleH2 * q1q3CircleCircleDY) /
          q1q3CircleCircleD) +
      ((q1q3CircleCircleA * q1q3CircleCircleDY +
          Real.sqrt q1q3CircleCircleH2 * q1q3CircleCircleDX) /
        q1q3CircleCircleD) *
        ((q1q3CircleCircleA * q1q3CircleCircleDY +
            Real.sqrt q1q3CircleCircleH2 * q1q3CircleCircleDX) /
          q1q3CircleCircleD) =
      ((11 : ℝ) / 20) ^ 2 := by
  exact circleCircleUpper_left_algebra
    q1q3CircleCircleDX q1q3CircleCircleDY q1q3CircleCircleD
    q1q3CircleCircleA (Real.sqrt q1q3CircleCircleH2) ((11 : ℝ) / 20)
    rfl q1q3CircleCircle_A_sq_add_H_sq_q1 q1q3CircleCircleD_ne

private theorem q1q3CircleCircleLower_q1_coordinate :
    ((q1q3CircleCircleA * q1q3CircleCircleDX +
          Real.sqrt q1q3CircleCircleH2 * q1q3CircleCircleDY) /
        q1q3CircleCircleD) *
        ((q1q3CircleCircleA * q1q3CircleCircleDX +
            Real.sqrt q1q3CircleCircleH2 * q1q3CircleCircleDY) /
          q1q3CircleCircleD) +
      ((q1q3CircleCircleA * q1q3CircleCircleDY -
          Real.sqrt q1q3CircleCircleH2 * q1q3CircleCircleDX) /
        q1q3CircleCircleD) *
        ((q1q3CircleCircleA * q1q3CircleCircleDY -
            Real.sqrt q1q3CircleCircleH2 * q1q3CircleCircleDX) /
          q1q3CircleCircleD) =
      ((11 : ℝ) / 20) ^ 2 := by
  exact circleCircleLower_left_algebra
    q1q3CircleCircleDX q1q3CircleCircleDY q1q3CircleCircleD
    q1q3CircleCircleA (Real.sqrt q1q3CircleCircleH2) ((11 : ℝ) / 20)
    rfl q1q3CircleCircle_A_sq_add_H_sq_q1 q1q3CircleCircleD_ne

private theorem q1q3CircleCircleUpper_q3_coordinate :
    (q1q3Q1CenterX +
          (q1q3CircleCircleA * q1q3CircleCircleDX -
              Real.sqrt q1q3CircleCircleH2 * q1q3CircleCircleDY) /
            q1q3CircleCircleD -
        q1q3Q3CenterX) *
        (q1q3Q1CenterX +
            (q1q3CircleCircleA * q1q3CircleCircleDX -
                Real.sqrt q1q3CircleCircleH2 * q1q3CircleCircleDY) /
              q1q3CircleCircleD -
          q1q3Q3CenterX) +
      (q1q3Q1CenterY +
            (q1q3CircleCircleA * q1q3CircleCircleDY +
                Real.sqrt q1q3CircleCircleH2 * q1q3CircleCircleDX) /
              q1q3CircleCircleD -
          q1q3Q3CenterY) *
        (q1q3Q1CenterY +
            (q1q3CircleCircleA * q1q3CircleCircleDY +
                Real.sqrt q1q3CircleCircleH2 * q1q3CircleCircleDX) /
              q1q3CircleCircleD -
          q1q3Q3CenterY) =
      (100 : ℝ) ^ 2 := by
  have h := circleCircleUpper_right_algebra
    q1q3CircleCircleDX q1q3CircleCircleDY q1q3CircleCircleD
    q1q3CircleCircleA (Real.sqrt q1q3CircleCircleH2) 100
    rfl q1q3CircleCircle_A_sub_D_sq_add_H_sq_q3 q1q3CircleCircleD_ne
  unfold q1q3CircleCircleDX q1q3CircleCircleDY at h
  convert h using 1
  all_goals ring

private theorem q1q3CircleCircleLower_q3_coordinate :
    (q1q3Q1CenterX +
          (q1q3CircleCircleA * q1q3CircleCircleDX +
              Real.sqrt q1q3CircleCircleH2 * q1q3CircleCircleDY) /
            q1q3CircleCircleD -
        q1q3Q3CenterX) *
        (q1q3Q1CenterX +
            (q1q3CircleCircleA * q1q3CircleCircleDX +
                Real.sqrt q1q3CircleCircleH2 * q1q3CircleCircleDY) /
              q1q3CircleCircleD -
          q1q3Q3CenterX) +
      (q1q3Q1CenterY +
            (q1q3CircleCircleA * q1q3CircleCircleDY -
                Real.sqrt q1q3CircleCircleH2 * q1q3CircleCircleDX) /
              q1q3CircleCircleD -
          q1q3Q3CenterY) *
        (q1q3Q1CenterY +
            (q1q3CircleCircleA * q1q3CircleCircleDY -
                Real.sqrt q1q3CircleCircleH2 * q1q3CircleCircleDX) /
              q1q3CircleCircleD -
          q1q3Q3CenterY) =
      (100 : ℝ) ^ 2 := by
  have h := circleCircleLower_right_algebra
    q1q3CircleCircleDX q1q3CircleCircleDY q1q3CircleCircleD
    q1q3CircleCircleA (Real.sqrt q1q3CircleCircleH2) 100
    rfl q1q3CircleCircle_A_sub_D_sq_add_H_sq_q3 q1q3CircleCircleD_ne
  unfold q1q3CircleCircleDX q1q3CircleCircleDY at h
  convert h using 1
  all_goals ring

theorem q1q3CircleCircleUpperPoint_mem_q1_circle :
    q1q3CircleCircleUpperPoint ∈
      circleSet karlssonOEISQ1.center karlssonOEISQ1.radius := by
  unfold q1q3CircleCircleUpperPoint circleSet distSq2 normSq2 dot2
  rw [q1q3_q1_center_eq]
  simp [karlssonOEISQ1, EuclideanLollipop.fromCenter, point2]
  convert q1q3CircleCircleUpper_q1_coordinate using 1
  all_goals norm_num

theorem q1q3CircleCircleLowerPoint_mem_q1_circle :
    q1q3CircleCircleLowerPoint ∈
      circleSet karlssonOEISQ1.center karlssonOEISQ1.radius := by
  unfold q1q3CircleCircleLowerPoint circleSet distSq2 normSq2 dot2
  rw [q1q3_q1_center_eq]
  simp [karlssonOEISQ1, EuclideanLollipop.fromCenter, point2]
  convert q1q3CircleCircleLower_q1_coordinate using 1
  all_goals norm_num

theorem q1q3CircleCircleUpperPoint_mem_q3_circle :
    q1q3CircleCircleUpperPoint ∈
      circleSet karlssonOEISQ3.center karlssonOEISQ3.radius := by
  unfold q1q3CircleCircleUpperPoint circleSet distSq2 normSq2 dot2
  rw [q1q3_q3_center_eq]
  simp [karlssonOEISQ3, EuclideanLollipop.fromAnchor, point2]
  exact q1q3CircleCircleUpper_q3_coordinate

theorem q1q3CircleCircleLowerPoint_mem_q3_circle :
    q1q3CircleCircleLowerPoint ∈
      circleSet karlssonOEISQ3.center karlssonOEISQ3.radius := by
  unfold q1q3CircleCircleLowerPoint circleSet distSq2 normSq2 dot2
  rw [q1q3_q3_center_eq]
  simp [karlssonOEISQ3, EuclideanLollipop.fromAnchor, point2]
  exact q1q3CircleCircleLower_q3_coordinate

theorem q1q3CircleCircleUpperPoint_mem_euclideanCircleCircleSet :
    toEuclideanR2 q1q3CircleCircleUpperPoint ∈
      euclideanCircleCircleSet karlssonOEISQ1 karlssonOEISQ3 :=
  mem_euclideanCircleCircleSet_of_mem_circleSets
    q1q3CircleCircleUpperPoint_mem_q1_circle
    q1q3CircleCircleUpperPoint_mem_q3_circle

theorem q1q3CircleCircleLowerPoint_mem_euclideanCircleCircleSet :
    toEuclideanR2 q1q3CircleCircleLowerPoint ∈
      euclideanCircleCircleSet karlssonOEISQ1 karlssonOEISQ3 :=
  mem_euclideanCircleCircleSet_of_mem_circleSets
    q1q3CircleCircleLowerPoint_mem_q1_circle
    q1q3CircleCircleLowerPoint_mem_q3_circle

theorem q1q3CircleCircleUpperPoint_mem_base_pairIntersectionSet :
    q1q3CircleCircleUpperPoint ∈
      karlssonOEISBaseArrangement.pairIntersectionSet
        (1 : Fin 4) (3 : Fin 4) := by
  exact
    OEISSevenPoint.pair_mem_of_euclideanCircleCircle
      (i := (1 : Fin 4)) (j := (3 : Fin 4))
      (p := q1q3CircleCircleUpperPoint)
      (by
        simpa [karlssonOEISBaseArrangement] using
          q1q3CircleCircleUpperPoint_mem_euclideanCircleCircleSet)

theorem q1q3CircleCircleLowerPoint_mem_base_pairIntersectionSet :
    q1q3CircleCircleLowerPoint ∈
      karlssonOEISBaseArrangement.pairIntersectionSet
        (1 : Fin 4) (3 : Fin 4) := by
  exact
    OEISSevenPoint.pair_mem_of_euclideanCircleCircle
      (i := (1 : Fin 4)) (j := (3 : Fin 4))
      (p := q1q3CircleCircleLowerPoint)
      (by
        simpa [karlssonOEISBaseArrangement] using
          q1q3CircleCircleLowerPoint_mem_euclideanCircleCircleSet)

private theorem q1q3CircleRay_sqrt_lt_dot :
    Real.sqrt q1q3CircleRayDiscriminant < q1q3CircleRayDot := by
  rw [Real.sqrt_lt q1q3CircleRayDiscriminant_nonneg
    q1q3CircleRayDot_pos.le]
  unfold q1q3CircleRayDiscriminant
  nlinarith [q1q3CircleRayConstant_pos]

theorem q1q3CircleRayNearTime_pos :
    0 < q1q3CircleRayNearTime := by
  unfold q1q3CircleRayNearTime
  nlinarith [q1q3CircleRay_sqrt_lt_dot]

theorem q1q3CircleRayFarTime_pos :
    0 < q1q3CircleRayFarTime := by
  unfold q1q3CircleRayFarTime
  nlinarith [q1q3CircleRayDot_pos,
    Real.sqrt_nonneg q1q3CircleRayDiscriminant]

private theorem q1q3RayCircle_sqrt_lt_dot :
    Real.sqrt q1q3RayCircleDiscriminant < q1q3RayCircleDot := by
  rw [Real.sqrt_lt q1q3RayCircleDiscriminant_nonneg
    q1q3RayCircleDot_pos.le]
  unfold q1q3RayCircleDiscriminant
  nlinarith [q1q3RayCircleConstant_pos]

theorem q1q3RayCircleNearTime_pos :
    0 < q1q3RayCircleNearTime := by
  unfold q1q3RayCircleNearTime
  nlinarith [q1q3RayCircle_sqrt_lt_dot]

theorem q1q3RayCircleFarTime_pos :
    0 < q1q3RayCircleFarTime := by
  unfold q1q3RayCircleFarTime
  nlinarith [q1q3RayCircleDot_pos,
    Real.sqrt_nonneg q1q3RayCircleDiscriminant]

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

private theorem q3_ray_point_not_mem_q3_circle_of_time_pos
    {t : ℝ} (ht : 0 < t) :
    karlssonOEISQ3.anchor + t • karlssonOEISQ3.rayDirection ∉
      circleSet karlssonOEISQ3.center karlssonOEISQ3.radius := by
  intro hp
  unfold circleSet distSq2 normSq2 dot2 at hp
  simp [karlssonOEISQ3, EuclideanLollipop.fromAnchor, angleDirection,
    point2, q3_theta_cos, q3_theta_sin] at hp
  ring_nf at hp
  have htrig :
      Real.sin (Real.pi * (1 / 30 : ℝ)) ^ 2 +
          Real.cos (Real.pi * (1 / 30 : ℝ)) ^ 2 = 1 :=
    Real.sin_sq_add_cos_sq (Real.pi * (1 / 30 : ℝ))
  nlinarith [htrig, ht, hp]

theorem q1q3CircleRayNearPoint_not_mem_q3_circle :
    q1q3CircleRayNearPoint ∉
      circleSet karlssonOEISQ3.center karlssonOEISQ3.radius := by
  unfold q1q3CircleRayNearPoint
  exact q3_ray_point_not_mem_q3_circle_of_time_pos
    q1q3CircleRayNearTime_pos

theorem q1q3CircleRayFarPoint_not_mem_q3_circle :
    q1q3CircleRayFarPoint ∉
      circleSet karlssonOEISQ3.center karlssonOEISQ3.radius := by
  unfold q1q3CircleRayFarPoint
  exact q3_ray_point_not_mem_q3_circle_of_time_pos
    q1q3CircleRayFarTime_pos

theorem q1q3RayCircleNearPoint_not_mem_q1_circle :
    q1q3RayCircleNearPoint ∉
      circleSet karlssonOEISQ1.center karlssonOEISQ1.radius := by
  unfold q1q3RayCircleNearPoint
  exact q1_ray_point_not_mem_q1_circle_of_time_pos
    q1q3RayCircleNearTime_pos

theorem q1q3RayCircleFarPoint_not_mem_q1_circle :
    q1q3RayCircleFarPoint ∉
      circleSet karlssonOEISQ1.center karlssonOEISQ1.radius := by
  unfold q1q3RayCircleFarPoint
  exact q1_ray_point_not_mem_q1_circle_of_time_pos
    q1q3RayCircleFarTime_pos

theorem q1q3RayRayPoint_not_mem_q1_circle :
    q1q3RayRayPoint ∉
      circleSet karlssonOEISQ1.center karlssonOEISQ1.radius := by
  unfold q1q3RayRayPoint
  exact q1_ray_point_not_mem_q1_circle_of_time_pos
    q1q3RayRayTimeQ1_pos

theorem q1q3RayRayPoint_not_mem_q3_circle :
    q1q3RayRayPoint ∉
      circleSet karlssonOEISQ3.center karlssonOEISQ3.radius := by
  rw [q1q3RayRayPoint_eq_q3_ray_expression]
  exact q3_ray_point_not_mem_q3_circle_of_time_pos
    q1q3RayRayTimeQ3_pos

private theorem q1q3CircleCircleDX_pos :
    0 < q1q3CircleCircleDX := by
  unfold q1q3CircleCircleDX q1q3Q3CenterX q1q3Q1CenterX
  have hanchor : 0 < karlssonOEISQ3AnchorX - (45 : ℝ) / 100 := by
    norm_num [karlssonOEISQ3AnchorX]
  nlinarith [hanchor, sin_beta_pos]

theorem q1q3CircleCircleUpperPoint_ne_lower :
    q1q3CircleCircleUpperPoint ≠ q1q3CircleCircleLowerPoint := by
  intro h
  have hy := congr_fun h 1
  unfold q1q3CircleCircleUpperPoint q1q3CircleCircleLowerPoint at hy
  simp [point2] at hy
  have hH : 0 < Real.sqrt q1q3CircleCircleH2 :=
    Real.sqrt_pos.2 q1q3CircleCircleH2_pos
  have hdiff :
      ((q1q3CircleCircleA * q1q3CircleCircleDY +
            Real.sqrt q1q3CircleCircleH2 * q1q3CircleCircleDX) /
          q1q3CircleCircleD) -
        ((q1q3CircleCircleA * q1q3CircleCircleDY -
            Real.sqrt q1q3CircleCircleH2 * q1q3CircleCircleDX) /
          q1q3CircleCircleD) = 0 := by
    nlinarith [hy]
  have hdiff_eval :
      ((q1q3CircleCircleA * q1q3CircleCircleDY +
            Real.sqrt q1q3CircleCircleH2 * q1q3CircleCircleDX) /
          q1q3CircleCircleD) -
        ((q1q3CircleCircleA * q1q3CircleCircleDY -
            Real.sqrt q1q3CircleCircleH2 * q1q3CircleCircleDX) /
          q1q3CircleCircleD) =
        (2 * Real.sqrt q1q3CircleCircleH2 *
            q1q3CircleCircleDX) / q1q3CircleCircleD := by
    field_simp [q1q3CircleCircleD_ne]
    ring
  have hpos :
      0 <
        (2 * Real.sqrt q1q3CircleCircleH2 *
            q1q3CircleCircleDX) / q1q3CircleCircleD := by
    exact div_pos
      (mul_pos (mul_pos (by norm_num) hH) q1q3CircleCircleDX_pos)
      q1q3CircleCircleD_pos
  rw [hdiff_eval] at hdiff
  nlinarith

theorem q1q3CircleRayNearPoint_ne_far :
    q1q3CircleRayNearPoint ≠ q1q3CircleRayFarPoint := by
  intro h
  have hy := congr_fun h 1
  unfold q1q3CircleRayNearPoint q1q3CircleRayFarPoint
    q1q3CircleRayNearTime q1q3CircleRayFarTime at hy
  simp [karlssonOEISQ3, EuclideanLollipop.fromAnchor, angleDirection,
    point2, q3_theta_sin] at hy
  have hsqrt : 0 < Real.sqrt q1q3CircleRayDiscriminant :=
    Real.sqrt_pos.2 q1q3CircleRayDiscriminant_pos
  rcases hy with htime | hcos
  · nlinarith [hsqrt, htime]
  · exact cos_beta_pos.ne' hcos

theorem q1q3RayCircleNearPoint_ne_far :
    q1q3RayCircleNearPoint ≠ q1q3RayCircleFarPoint := by
  intro h
  have hx := congr_fun h 0
  unfold q1q3RayCircleNearPoint q1q3RayCircleFarPoint
    q1q3RayCircleNearTime q1q3RayCircleFarTime at hx
  simp [karlssonOEISQ1, EuclideanLollipop.fromCenter, angleDirection,
    point2, Real.cos_neg] at hx
  have hsqrt : 0 < Real.sqrt q1q3RayCircleDiscriminant :=
    Real.sqrt_pos.2 q1q3RayCircleDiscriminant_pos
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

private theorem ne_of_left_mem_q3_circle_of_right_not_mem_q3_circle
    {p q : R2}
    (hp : p ∈ circleSet karlssonOEISQ3.center karlssonOEISQ3.radius)
    (hq : q ∉ circleSet karlssonOEISQ3.center karlssonOEISQ3.radius) :
    p ≠ q := by
  intro h
  exact hq (by simpa [h] using hp)

theorem q1q3CircleCircleUpperPoint_ne_circleRayNear :
    q1q3CircleCircleUpperPoint ≠ q1q3CircleRayNearPoint :=
  ne_of_left_mem_q3_circle_of_right_not_mem_q3_circle
    q1q3CircleCircleUpperPoint_mem_q3_circle
    q1q3CircleRayNearPoint_not_mem_q3_circle

theorem q1q3CircleCircleUpperPoint_ne_circleRayFar :
    q1q3CircleCircleUpperPoint ≠ q1q3CircleRayFarPoint :=
  ne_of_left_mem_q3_circle_of_right_not_mem_q3_circle
    q1q3CircleCircleUpperPoint_mem_q3_circle
    q1q3CircleRayFarPoint_not_mem_q3_circle

theorem q1q3CircleCircleUpperPoint_ne_rayCircleNear :
    q1q3CircleCircleUpperPoint ≠ q1q3RayCircleNearPoint :=
  ne_of_left_mem_q1_circle_of_right_not_mem_q1_circle
    q1q3CircleCircleUpperPoint_mem_q1_circle
    q1q3RayCircleNearPoint_not_mem_q1_circle

theorem q1q3CircleCircleUpperPoint_ne_rayCircleFar :
    q1q3CircleCircleUpperPoint ≠ q1q3RayCircleFarPoint :=
  ne_of_left_mem_q1_circle_of_right_not_mem_q1_circle
    q1q3CircleCircleUpperPoint_mem_q1_circle
    q1q3RayCircleFarPoint_not_mem_q1_circle

theorem q1q3CircleCircleUpperPoint_ne_rayRay :
    q1q3CircleCircleUpperPoint ≠ q1q3RayRayPoint :=
  ne_of_left_mem_q1_circle_of_right_not_mem_q1_circle
    q1q3CircleCircleUpperPoint_mem_q1_circle
    q1q3RayRayPoint_not_mem_q1_circle

theorem q1q3CircleCircleLowerPoint_ne_circleRayNear :
    q1q3CircleCircleLowerPoint ≠ q1q3CircleRayNearPoint :=
  ne_of_left_mem_q3_circle_of_right_not_mem_q3_circle
    q1q3CircleCircleLowerPoint_mem_q3_circle
    q1q3CircleRayNearPoint_not_mem_q3_circle

theorem q1q3CircleCircleLowerPoint_ne_circleRayFar :
    q1q3CircleCircleLowerPoint ≠ q1q3CircleRayFarPoint :=
  ne_of_left_mem_q3_circle_of_right_not_mem_q3_circle
    q1q3CircleCircleLowerPoint_mem_q3_circle
    q1q3CircleRayFarPoint_not_mem_q3_circle

theorem q1q3CircleCircleLowerPoint_ne_rayCircleNear :
    q1q3CircleCircleLowerPoint ≠ q1q3RayCircleNearPoint :=
  ne_of_left_mem_q1_circle_of_right_not_mem_q1_circle
    q1q3CircleCircleLowerPoint_mem_q1_circle
    q1q3RayCircleNearPoint_not_mem_q1_circle

theorem q1q3CircleCircleLowerPoint_ne_rayCircleFar :
    q1q3CircleCircleLowerPoint ≠ q1q3RayCircleFarPoint :=
  ne_of_left_mem_q1_circle_of_right_not_mem_q1_circle
    q1q3CircleCircleLowerPoint_mem_q1_circle
    q1q3RayCircleFarPoint_not_mem_q1_circle

theorem q1q3CircleCircleLowerPoint_ne_rayRay :
    q1q3CircleCircleLowerPoint ≠ q1q3RayRayPoint :=
  ne_of_left_mem_q1_circle_of_right_not_mem_q1_circle
    q1q3CircleCircleLowerPoint_mem_q1_circle
    q1q3RayRayPoint_not_mem_q1_circle

theorem q1q3CircleRayNearPoint_ne_rayCircleNear :
    q1q3CircleRayNearPoint ≠ q1q3RayCircleNearPoint :=
  ne_of_left_mem_q1_circle_of_right_not_mem_q1_circle
    q1q3CircleRayNearPoint_mem_q1_circle
    q1q3RayCircleNearPoint_not_mem_q1_circle

theorem q1q3CircleRayNearPoint_ne_rayCircleFar :
    q1q3CircleRayNearPoint ≠ q1q3RayCircleFarPoint :=
  ne_of_left_mem_q1_circle_of_right_not_mem_q1_circle
    q1q3CircleRayNearPoint_mem_q1_circle
    q1q3RayCircleFarPoint_not_mem_q1_circle

theorem q1q3CircleRayNearPoint_ne_rayRay :
    q1q3CircleRayNearPoint ≠ q1q3RayRayPoint :=
  ne_of_left_mem_q1_circle_of_right_not_mem_q1_circle
    q1q3CircleRayNearPoint_mem_q1_circle
    q1q3RayRayPoint_not_mem_q1_circle

theorem q1q3CircleRayFarPoint_ne_rayCircleNear :
    q1q3CircleRayFarPoint ≠ q1q3RayCircleNearPoint :=
  ne_of_left_mem_q1_circle_of_right_not_mem_q1_circle
    q1q3CircleRayFarPoint_mem_q1_circle
    q1q3RayCircleNearPoint_not_mem_q1_circle

theorem q1q3CircleRayFarPoint_ne_rayCircleFar :
    q1q3CircleRayFarPoint ≠ q1q3RayCircleFarPoint :=
  ne_of_left_mem_q1_circle_of_right_not_mem_q1_circle
    q1q3CircleRayFarPoint_mem_q1_circle
    q1q3RayCircleFarPoint_not_mem_q1_circle

theorem q1q3CircleRayFarPoint_ne_rayRay :
    q1q3CircleRayFarPoint ≠ q1q3RayRayPoint :=
  ne_of_left_mem_q1_circle_of_right_not_mem_q1_circle
    q1q3CircleRayFarPoint_mem_q1_circle
    q1q3RayRayPoint_not_mem_q1_circle

theorem q1q3RayCircleNearPoint_ne_rayRay :
    q1q3RayCircleNearPoint ≠ q1q3RayRayPoint :=
  ne_of_left_mem_q3_circle_of_right_not_mem_q3_circle
    q1q3RayCircleNearPoint_mem_q3_circle
    q1q3RayRayPoint_not_mem_q3_circle

theorem q1q3RayCircleFarPoint_ne_rayRay :
    q1q3RayCircleFarPoint ≠ q1q3RayRayPoint :=
  ne_of_left_mem_q3_circle_of_right_not_mem_q3_circle
    q1q3RayCircleFarPoint_mem_q3_circle
    q1q3RayRayPoint_not_mem_q3_circle

noncomputable def q1q3SevenPointFinset : Finset R2 :=
  {q1q3CircleCircleUpperPoint, q1q3CircleCircleLowerPoint,
    q1q3CircleRayNearPoint, q1q3CircleRayFarPoint,
    q1q3RayCircleNearPoint, q1q3RayCircleFarPoint,
    q1q3RayRayPoint}

theorem q1q3SevenPointFinset_card :
    q1q3SevenPointFinset.card = 7 := by
  classical
  simp [q1q3SevenPointFinset,
    q1q3CircleCircleUpperPoint_ne_lower,
    q1q3CircleCircleUpperPoint_ne_circleRayNear,
    q1q3CircleCircleUpperPoint_ne_circleRayFar,
    q1q3CircleCircleUpperPoint_ne_rayCircleNear,
    q1q3CircleCircleUpperPoint_ne_rayCircleFar,
    q1q3CircleCircleUpperPoint_ne_rayRay,
    q1q3CircleCircleLowerPoint_ne_circleRayNear,
    q1q3CircleCircleLowerPoint_ne_circleRayFar,
    q1q3CircleCircleLowerPoint_ne_rayCircleNear,
    q1q3CircleCircleLowerPoint_ne_rayCircleFar,
    q1q3CircleCircleLowerPoint_ne_rayRay,
    q1q3CircleRayNearPoint_ne_far,
    q1q3CircleRayNearPoint_ne_rayCircleNear,
    q1q3CircleRayNearPoint_ne_rayCircleFar,
    q1q3CircleRayNearPoint_ne_rayRay,
    q1q3CircleRayFarPoint_ne_rayCircleNear,
    q1q3CircleRayFarPoint_ne_rayCircleFar,
    q1q3CircleRayFarPoint_ne_rayRay,
    q1q3RayCircleNearPoint_ne_far,
    q1q3RayCircleNearPoint_ne_rayRay,
    q1q3RayCircleFarPoint_ne_rayRay]

theorem q1q3SevenPointFinset_subset :
    ∀ p ∈ q1q3SevenPointFinset,
      p ∈ karlssonOEISBaseArrangement.pairIntersectionSet
        (1 : Fin 4) (3 : Fin 4) := by
  intro p hp
  simp [q1q3SevenPointFinset] at hp
  rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact q1q3CircleCircleUpperPoint_mem_base_pairIntersectionSet
  · exact q1q3CircleCircleLowerPoint_mem_base_pairIntersectionSet
  · exact q1q3CircleRayNearPoint_mem_base_pairIntersectionSet
  · exact q1q3CircleRayFarPoint_mem_base_pairIntersectionSet
  · exact q1q3RayCircleNearPoint_mem_base_pairIntersectionSet
  · exact q1q3RayCircleFarPoint_mem_base_pairIntersectionSet
  · exact q1q3RayRayPoint_mem_base_pairIntersectionSet

noncomputable def q1q3SevenPointSubset :
    OEISSevenPoint.SevenPointSubset (1 : Fin 4) (3 : Fin 4) where
  points := q1q3SevenPointFinset
  card_eq_seven := q1q3SevenPointFinset_card
  points_subset := q1q3SevenPointFinset_subset

noncomputable def q1q3PairCoordinateCrossingCertificate :
    KarlssonOEISBasePairCoordinateCrossingCertificate
      (1 : Fin 4) (3 : Fin 4) (by decide) :=
  OEISSevenPoint.pair13Certificate q1q3SevenPointSubset

end

end OEISPair13
end CompleteFormalization
end TheoremOneManuscript
end Lollipop
