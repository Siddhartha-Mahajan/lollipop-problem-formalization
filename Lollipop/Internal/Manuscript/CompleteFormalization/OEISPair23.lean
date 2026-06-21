import Lollipop.Internal.Manuscript.CompleteFormalization.OEISSevenPoint
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.Analysis.Real.Sqrt
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds

/-!
Concrete component witnesses for the OEIS/Karlsson base pair `(Q2,Q3)`.

This file completes the exact `= 7` work for `(Q2,Q3)`: two circle-circle
points, two circle-ray points, two ray-circle points, and one ray-ray point.
The ray-ray calculation uses the useful determinant `-sin (pi/6) = -1/2`, so
the intersection times have compact formulas.
-/

namespace Lollipop
namespace TheoremOneManuscript
namespace CompleteFormalization

open PrimitiveGeometry

namespace OEISPair23

noncomputable section

open ExplicitInputs
open TheoremOneEndToEnd.PaulsenLinearAlgebra (distSq2 normSq2 dot2)

private abbrev alpha : ℝ := 2 * Real.pi / 15
private abbrev beta : ℝ := Real.pi / 30

private theorem alpha_pos : 0 < alpha := by
  dsimp [alpha]
  nlinarith [Real.pi_pos]

private theorem beta_pos : 0 < beta := by
  dsimp [beta]
  nlinarith [Real.pi_pos]

private theorem alpha_lt_pi_div_four : alpha < Real.pi / 4 := by
  dsimp [alpha]
  nlinarith [Real.pi_pos]

private theorem alpha_lt_pi_div_two : alpha < Real.pi / 2 := by
  exact alpha_lt_pi_div_four.trans (by nlinarith [Real.pi_pos])

private theorem beta_lt_pi_div_four : beta < Real.pi / 4 := by
  dsimp [beta]
  nlinarith [Real.pi_pos]

private theorem beta_lt_pi_div_two : beta < Real.pi / 2 := by
  exact beta_lt_pi_div_four.trans (by nlinarith [Real.pi_pos])

private theorem cos_alpha_pos : 0 < Real.cos alpha := by
  apply Real.cos_pos_of_mem_Ioo
  constructor
  · nlinarith [alpha_pos, Real.pi_pos]
  · exact alpha_lt_pi_div_two

private theorem sin_alpha_pos : 0 < Real.sin alpha := by
  apply Real.sin_pos_of_pos_of_lt_pi
  · exact alpha_pos
  · nlinarith [alpha_lt_pi_div_two, Real.pi_pos]

private theorem cos_beta_pos : 0 < Real.cos beta := by
  apply Real.cos_pos_of_mem_Ioo
  constructor
  · nlinarith [beta_pos, Real.pi_pos]
  · exact beta_lt_pi_div_two

private theorem sin_beta_pos : 0 < Real.sin beta := by
  apply Real.sin_pos_of_pos_of_lt_pi
  · exact beta_pos
  · nlinarith [beta_lt_pi_div_two, Real.pi_pos]

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

private theorem alpha_add_beta_eq_pi_div_six :
    alpha + beta = Real.pi / 6 := by
  dsimp [alpha, beta]
  ring

private theorem sin_alpha_cos_beta_add_cos_alpha_sin_beta_eq_half :
    Real.sin alpha * Real.cos beta +
      Real.cos alpha * Real.sin beta = (1 : ℝ) / 2 := by
  have hsin : Real.sin (alpha + beta) = (1 : ℝ) / 2 := by
    rw [alpha_add_beta_eq_pi_div_six, Real.sin_pi_div_six]
  rw [Real.sin_add] at hsin
  exact hsin

private theorem cos_alpha_cos_beta_sub_sin_alpha_sin_beta_eq_sqrt_three_div_two :
    Real.cos alpha * Real.cos beta -
      Real.sin alpha * Real.sin beta = Real.sqrt 3 / 2 := by
  have hcos : Real.cos (alpha + beta) = Real.sqrt 3 / 2 := by
    rw [alpha_add_beta_eq_pi_div_six, Real.cos_pi_div_six]
  rw [Real.cos_add] at hcos
  exact hcos

private theorem one_half_lt_cos_alpha_cos_beta_sub_sin_alpha_sin_beta :
    (1 : ℝ) / 2 <
      Real.cos alpha * Real.cos beta -
        Real.sin alpha * Real.sin beta := by
  rw [cos_alpha_cos_beta_sub_sin_alpha_sin_beta_eq_sqrt_three_div_two]
  have hsqrt_sq : (Real.sqrt (3 : ℝ)) ^ 2 = 3 := by
    rw [Real.sq_sqrt]
    norm_num
  have hsqrt_nonneg : 0 ≤ Real.sqrt (3 : ℝ) :=
    Real.sqrt_nonneg 3
  nlinarith

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

private theorem one_half_lt_cos_alpha :
    (1 : ℝ) / 2 < Real.cos alpha := by
  have h :
      Real.cos (Real.pi / 3) < Real.cos alpha :=
    Real.cos_lt_cos_of_nonneg_of_le_pi
      alpha_pos.le
      (by nlinarith [Real.pi_pos])
      (by
        dsimp [alpha]
        nlinarith [Real.pi_pos])
  simpa [Real.cos_pi_div_three] using h

private theorem nine_div_ten_lt_cos_beta :
    (9 : ℝ) / 10 < Real.cos beta := by
  have hcos := Real.one_sub_sq_div_two_lt_cos (x := beta) beta_pos.ne'
  have hbeta_lt : beta < (2 : ℝ) / 15 := by
    dsimp [beta]
    nlinarith [Real.pi_lt_four]
  nlinarith [hcos, beta_pos, hbeta_lt]

private theorem nine_div_ten_lt_cos_alpha :
    (9 : ℝ) / 10 < Real.cos alpha := by
  have hcos := Real.one_sub_sq_div_two_lt_cos (x := alpha) alpha_pos.ne'
  have halpha_lt : alpha < (21 : ℝ) / 50 := by
    dsimp [alpha]
    nlinarith [Real.pi_lt_d2]
  nlinarith [hcos, alpha_pos, halpha_lt]

private theorem cos_alpha_cos_beta_sub_sin_alpha_sin_beta_lt_nine_div_ten :
    Real.cos alpha * Real.cos beta -
        Real.sin alpha * Real.sin beta < (9 : ℝ) / 10 := by
  rw [cos_alpha_cos_beta_sub_sin_alpha_sin_beta_eq_sqrt_three_div_two]
  have hsqrt_sq : (Real.sqrt (3 : ℝ)) ^ 2 = 3 := by
    rw [Real.sq_sqrt]
    norm_num
  have hsqrt_nonneg : 0 ≤ Real.sqrt (3 : ℝ) :=
    Real.sqrt_nonneg 3
  nlinarith

/-- Horizontal separation from the `Q3` anchor to the `Q2` anchor. -/
private abbrev q2q3DeltaX : ℝ :=
  (23 : ℝ) / 20 - karlssonOEISQ3AnchorX

private theorem q2q3DeltaX_pos : 0 < q2q3DeltaX := by
  norm_num [q2q3DeltaX, karlssonOEISQ3AnchorX]

private theorem q2q3DeltaX_lt_fourteen_div_seventy_five :
    q2q3DeltaX < (14 : ℝ) / 75 := by
  norm_num [q2q3DeltaX, karlssonOEISQ3AnchorX]

private theorem q2q3DeltaX_lt_one :
    q2q3DeltaX < 1 := by
  nlinarith [q2q3DeltaX_lt_fourteen_div_seventy_five]

private theorem q2q3DeltaX_sq_lt_one :
    q2q3DeltaX ^ 2 < 1 := by
  nlinarith [q2q3DeltaX_pos, q2q3DeltaX_lt_one]

private theorem q2q3_delta_mul_sin_alpha_lt_fourteen_div_seventy_five :
    q2q3DeltaX * Real.sin alpha < (14 : ℝ) / 75 := by
  have hmul_le :
      q2q3DeltaX * Real.sin alpha ≤ q2q3DeltaX * 1 :=
    mul_le_mul_of_nonneg_left (Real.sin_le_one alpha) q2q3DeltaX_pos.le
  nlinarith [hmul_le, q2q3DeltaX_lt_fourteen_div_seventy_five]

private theorem q2q3_delta_mul_sin_beta_lt_fourteen_div_seventy_five :
    q2q3DeltaX * Real.sin beta < (14 : ℝ) / 75 := by
  have hmul_le :
      q2q3DeltaX * Real.sin beta ≤ q2q3DeltaX * 1 :=
    mul_le_mul_of_nonneg_left (Real.sin_le_one beta) q2q3DeltaX_pos.le
  nlinarith [hmul_le, q2q3DeltaX_lt_fourteen_div_seventy_five]

private theorem q2q3_delta_mul_sin_beta_lt_one :
    q2q3DeltaX * Real.sin beta < 1 := by
  nlinarith [q2q3_delta_mul_sin_beta_lt_fourteen_div_seventy_five]

private theorem four_div_fifteen_le_sin_alpha :
    (4 : ℝ) / 15 ≤ Real.sin alpha := by
  have h := Real.mul_le_sin alpha_pos.le alpha_lt_pi_div_two.le
  have hleft : 2 / Real.pi * alpha = (4 : ℝ) / 15 := by
    dsimp [alpha]
    field_simp [Real.pi_pos.ne']
    ring
  simpa [hleft] using h

/-- Forward time along the `Q2` ray to the `Q2,Q3` ray-ray point. -/
noncomputable def q2q3RayRayTimeQ2 : ℝ :=
  2 * (q2q3DeltaX * Real.cos beta +
    ((7 : ℝ) / 10) * Real.sin beta)

/-- Forward time along the `Q3` ray to the same point. -/
noncomputable def q2q3RayRayTimeQ3 : ℝ :=
  2 * (((7 : ℝ) / 10) * Real.sin alpha -
    q2q3DeltaX * Real.cos alpha)

/-- The concrete ray-ray point for the OEIS/Karlsson pair `(Q2,Q3)`. -/
noncomputable def q2q3RayRayPoint : R2 :=
  karlssonOEISQ2.anchor + q2q3RayRayTimeQ2 • karlssonOEISQ2.rayDirection

theorem q2q3RayRayTimeQ2_pos : 0 < q2q3RayRayTimeQ2 := by
  unfold q2q3RayRayTimeQ2
  nlinarith [q2q3DeltaX_pos, cos_beta_pos, sin_beta_pos]

private theorem q2q3_delta_cos_alpha_lt_fourteen_div_seventy_five :
    q2q3DeltaX * Real.cos alpha < (14 : ℝ) / 75 := by
  have hcos_le : Real.cos alpha ≤ 1 := Real.cos_le_one alpha
  nlinarith [q2q3DeltaX_pos, cos_alpha_pos,
    q2q3DeltaX_lt_fourteen_div_seventy_five, hcos_le]

theorem q2q3RayRayTimeQ3_pos : 0 < q2q3RayRayTimeQ3 := by
  unfold q2q3RayRayTimeQ3
  have hsin :
      (14 : ℝ) / 75 ≤ ((7 : ℝ) / 10) * Real.sin alpha := by
    nlinarith [four_div_fifteen_le_sin_alpha]
  nlinarith [hsin, q2q3_delta_cos_alpha_lt_fourteen_div_seventy_five]

/-- The `Q2`-ray expression for the ray-ray point equals the `Q3`-ray
expression. -/
theorem q2q3RayRayPoint_eq_q3_ray_expression :
    q2q3RayRayPoint =
      karlssonOEISQ3.anchor +
        q2q3RayRayTimeQ3 • karlssonOEISQ3.rayDirection := by
  ext i
  fin_cases i
  · unfold q2q3RayRayPoint q2q3RayRayTimeQ2 q2q3RayRayTimeQ3 q2q3DeltaX
    simp [karlssonOEISQ2, karlssonOEISQ3, EuclideanLollipop.fromAnchor,
      angleDirection, point2, q2_theta_cos, q2_theta_sin, q3_theta_cos,
      q3_theta_sin]
    ring_nf
    have hsum := sin_alpha_cos_beta_add_cos_alpha_sin_beta_eq_half
    dsimp [alpha, beta] at hsum
    ring_nf at hsum
    have hsum_comm :
        Real.cos (Real.pi * (1 / 30)) * Real.sin (Real.pi * (2 / 15)) +
            Real.sin (Real.pi * (1 / 30)) * Real.cos (Real.pi * (2 / 15)) =
          (1 : ℝ) / 2 := by
      simpa [mul_comm, add_comm, add_left_comm, add_assoc] using hsum
    have hscaled :
        karlssonOEISQ3AnchorX *
            Real.cos (Real.pi * (1 / 30)) * Real.sin (Real.pi * (2 / 15)) +
          karlssonOEISQ3AnchorX *
            Real.sin (Real.pi * (1 / 30)) * Real.cos (Real.pi * (2 / 15)) =
          karlssonOEISQ3AnchorX / 2 := by
      calc
        karlssonOEISQ3AnchorX *
              Real.cos (Real.pi * (1 / 30)) * Real.sin (Real.pi * (2 / 15)) +
            karlssonOEISQ3AnchorX *
              Real.sin (Real.pi * (1 / 30)) * Real.cos (Real.pi * (2 / 15)) =
            karlssonOEISQ3AnchorX *
              (Real.cos (Real.pi * (1 / 30)) * Real.sin (Real.pi * (2 / 15)) +
                Real.sin (Real.pi * (1 / 30)) * Real.cos (Real.pi * (2 / 15))) := by
              ring
        _ = karlssonOEISQ3AnchorX / 2 := by
              rw [hsum_comm]
              ring
    nlinarith [hsum_comm, hscaled]
  · unfold q2q3RayRayPoint q2q3RayRayTimeQ2 q2q3RayRayTimeQ3 q2q3DeltaX
    simp [karlssonOEISQ2, karlssonOEISQ3, EuclideanLollipop.fromAnchor,
      angleDirection, point2, q2_theta_cos, q2_theta_sin, q3_theta_cos,
      q3_theta_sin]
    ring_nf
    have hsum := sin_alpha_cos_beta_add_cos_alpha_sin_beta_eq_half
    dsimp [alpha, beta] at hsum
    ring_nf at hsum
    have hsum_comm :
        Real.cos (Real.pi * (1 / 30)) * Real.sin (Real.pi * (2 / 15)) +
            Real.sin (Real.pi * (1 / 30)) * Real.cos (Real.pi * (2 / 15)) =
          (1 : ℝ) / 2 := by
      simpa [mul_comm, add_comm, add_left_comm, add_assoc] using hsum
    nlinarith [hsum_comm]

theorem q2q3RayRayPoint_mem_q2_ray :
    q2q3RayRayPoint ∈
      raySet karlssonOEISQ2.anchor karlssonOEISQ2.rayDirection := by
  exact ⟨q2q3RayRayTimeQ2, q2q3RayRayTimeQ2_pos.le, rfl⟩

theorem q2q3RayRayPoint_mem_q3_ray :
    q2q3RayRayPoint ∈
      raySet karlssonOEISQ3.anchor karlssonOEISQ3.rayDirection := by
  exact ⟨q2q3RayRayTimeQ3, q2q3RayRayTimeQ3_pos.le,
    q2q3RayRayPoint_eq_q3_ray_expression⟩

/-- Lifted ray-ray component form of the concrete `(Q2,Q3)` ray-ray point. -/
theorem q2q3RayRayPoint_mem_euclideanRayRaySet :
    toEuclideanR2 q2q3RayRayPoint ∈
      euclideanRayRaySet karlssonOEISQ2 karlssonOEISQ3 :=
  mem_euclideanRayRaySet_of_mem_raySets
    q2q3RayRayPoint_mem_q2_ray q2q3RayRayPoint_mem_q3_ray

/-- Arrangement-indexed primitive carrier-intersection form. -/
theorem q2q3RayRayPoint_mem_base_pairIntersectionSet :
    q2q3RayRayPoint ∈
      karlssonOEISBaseArrangement.pairIntersectionSet
        (2 : Fin 4) (3 : Fin 4) := by
  exact
    OEISSevenPoint.pair_mem_of_euclideanRayRay
      (i := (2 : Fin 4)) (j := (3 : Fin 4))
      (p := q2q3RayRayPoint)
      (by
        simpa [karlssonOEISBaseArrangement] using
          q2q3RayRayPoint_mem_euclideanRayRaySet)

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

private theorem q2_rayDirection_normSq :
    normSq2 karlssonOEISQ2.rayDirection = 1 := by
  simpa [karlssonOEISQ2, EuclideanLollipop.fromAnchor] using
    normSq2_angleDirection karlssonOEISQ2Theta

private theorem q3_rayDirection_normSq :
    normSq2 karlssonOEISQ3.rayDirection = 1 := by
  simpa [karlssonOEISQ3, EuclideanLollipop.fromAnchor] using
    normSq2_angleDirection karlssonOEISQ3Theta

/-- Positive dot coefficient in the quadratic for
`circle(Q2) ∩ ray(Q3)`. -/
private abbrev q2q3CircleRayDot : ℝ :=
  -dot2 (karlssonOEISQ3.anchor - karlssonOEISQ2.center)
    karlssonOEISQ3.rayDirection

/-- Constant term in the quadratic for `circle(Q2) ∩ ray(Q3)`. -/
private abbrev q2q3CircleRayConstant : ℝ :=
  distSq2 karlssonOEISQ3.anchor karlssonOEISQ2.center -
    karlssonOEISQ2.radius ^ 2

/-- Discriminant for `circle(Q2) ∩ ray(Q3)`. -/
private abbrev q2q3CircleRayDiscriminant : ℝ :=
  q2q3CircleRayDot ^ 2 - q2q3CircleRayConstant

private theorem q2q3CircleRayDot_expanded :
    q2q3CircleRayDot =
      (100 : ℝ) *
          (Real.cos alpha * Real.cos beta -
            Real.sin alpha * Real.sin beta) +
        ((7 : ℝ) / 10) * Real.cos beta -
        q2q3DeltaX * Real.sin beta := by
  unfold q2q3CircleRayDot q2q3DeltaX dot2
  simp [karlssonOEISQ2, karlssonOEISQ3, EuclideanLollipop.fromAnchor,
    angleDirection, point2, q2_theta_cos, q2_theta_sin,
    q3_theta_cos, q3_theta_sin]
  ring

private theorem q2q3CircleRayConstant_expanded :
    q2q3CircleRayConstant =
      q2q3DeltaX ^ 2 + 200 * q2q3DeltaX * Real.sin alpha +
        (49 : ℝ) / 100 + 140 * Real.cos alpha := by
  unfold q2q3CircleRayConstant q2q3DeltaX distSq2 normSq2 dot2
  simp [karlssonOEISQ2, karlssonOEISQ3, EuclideanLollipop.fromAnchor,
    angleDirection, point2, q2_theta_cos, q2_theta_sin]
  ring_nf
  have htrig :
      Real.sin (Real.pi * (2 / 15 : ℝ)) ^ 2 +
          Real.cos (Real.pi * (2 / 15 : ℝ)) ^ 2 = 1 := by
    exact Real.sin_sq_add_cos_sq (Real.pi * (2 / 15 : ℝ))
  nlinarith [htrig]

private theorem q2q3CircleRayDot_gt_forty_nine :
    (49 : ℝ) < q2q3CircleRayDot := by
  rw [q2q3CircleRayDot_expanded]
  nlinarith [one_half_lt_cos_alpha_cos_beta_sub_sin_alpha_sin_beta,
    cos_beta_pos, q2q3_delta_mul_sin_beta_lt_one]

private theorem q2q3CircleRayDot_pos :
    0 < q2q3CircleRayDot := by
  nlinarith [q2q3CircleRayDot_gt_forty_nine]

private theorem q2q3CircleRayConstant_pos :
    0 < q2q3CircleRayConstant := by
  rw [q2q3CircleRayConstant_expanded]
  have hprod : 0 < 200 * q2q3DeltaX * Real.sin alpha := by
    have hcore : 0 < q2q3DeltaX * Real.sin alpha :=
      mul_pos q2q3DeltaX_pos sin_alpha_pos
    nlinarith
  nlinarith [sq_nonneg q2q3DeltaX, hprod, cos_alpha_pos]

private theorem q2q3CircleRayConstant_lt_two_hundred :
    q2q3CircleRayConstant < (200 : ℝ) := by
  rw [q2q3CircleRayConstant_expanded]
  have hcos_le : Real.cos alpha ≤ 1 := Real.cos_le_one alpha
  nlinarith [q2q3DeltaX_sq_lt_one,
    q2q3_delta_mul_sin_alpha_lt_fourteen_div_seventy_five, hcos_le]

private theorem q2q3CircleRayDiscriminant_pos :
    0 < q2q3CircleRayDiscriminant := by
  unfold q2q3CircleRayDiscriminant
  nlinarith [q2q3CircleRayDot_gt_forty_nine,
    q2q3CircleRayConstant_lt_two_hundred]

private theorem q2q3CircleRayDiscriminant_nonneg :
    0 ≤ q2q3CircleRayDiscriminant :=
  q2q3CircleRayDiscriminant_pos.le

private theorem q2q3CircleRay_sqrt_le_dot :
    Real.sqrt q2q3CircleRayDiscriminant ≤ q2q3CircleRayDot := by
  rw [Real.sqrt_le_iff]
  exact ⟨q2q3CircleRayDot_pos.le, by
    unfold q2q3CircleRayDiscriminant
    nlinarith [q2q3CircleRayConstant_pos]⟩

/-- Near forward time along the `Q3` ray at which it hits the `Q2` circle. -/
noncomputable def q2q3CircleRayNearTime : ℝ :=
  q2q3CircleRayDot - Real.sqrt q2q3CircleRayDiscriminant

/-- Far forward time along the `Q3` ray at which it hits the `Q2` circle. -/
noncomputable def q2q3CircleRayFarTime : ℝ :=
  q2q3CircleRayDot + Real.sqrt q2q3CircleRayDiscriminant

/-- Near intersection of `circle(Q2)` with the `Q3` ray. -/
noncomputable def q2q3CircleRayNearPoint : R2 :=
  karlssonOEISQ3.anchor +
    q2q3CircleRayNearTime • karlssonOEISQ3.rayDirection

/-- Far intersection of `circle(Q2)` with the `Q3` ray. -/
noncomputable def q2q3CircleRayFarPoint : R2 :=
  karlssonOEISQ3.anchor +
    q2q3CircleRayFarTime • karlssonOEISQ3.rayDirection

theorem q2q3CircleRayNearTime_nonneg :
    0 ≤ q2q3CircleRayNearTime := by
  unfold q2q3CircleRayNearTime
  nlinarith [q2q3CircleRay_sqrt_le_dot]

theorem q2q3CircleRayFarTime_nonneg :
    0 ≤ q2q3CircleRayFarTime := by
  unfold q2q3CircleRayFarTime
  nlinarith [q2q3CircleRayDot_pos,
    Real.sqrt_nonneg q2q3CircleRayDiscriminant]

private theorem q2q3CircleRayNearTime_quadratic :
    q2q3CircleRayNearTime ^ 2 -
        2 * q2q3CircleRayDot * q2q3CircleRayNearTime +
        q2q3CircleRayConstant = 0 := by
  unfold q2q3CircleRayNearTime q2q3CircleRayDiscriminant
  have hsqrt_sq :
      (Real.sqrt
          (q2q3CircleRayDot ^ 2 - q2q3CircleRayConstant)) ^ 2 =
        q2q3CircleRayDot ^ 2 - q2q3CircleRayConstant := by
    rw [Real.sq_sqrt]
    simpa [q2q3CircleRayDiscriminant] using
      q2q3CircleRayDiscriminant_nonneg
  nlinarith [hsqrt_sq]

private theorem q2q3CircleRayFarTime_quadratic :
    q2q3CircleRayFarTime ^ 2 -
        2 * q2q3CircleRayDot * q2q3CircleRayFarTime +
        q2q3CircleRayConstant = 0 := by
  unfold q2q3CircleRayFarTime q2q3CircleRayDiscriminant
  have hsqrt_sq :
      (Real.sqrt
          (q2q3CircleRayDot ^ 2 - q2q3CircleRayConstant)) ^ 2 =
        q2q3CircleRayDot ^ 2 - q2q3CircleRayConstant := by
    rw [Real.sq_sqrt]
    simpa [q2q3CircleRayDiscriminant] using
      q2q3CircleRayDiscriminant_nonneg
  nlinarith [hsqrt_sq]

theorem q2q3CircleRayNearPoint_mem_q2_circle :
    q2q3CircleRayNearPoint ∈
      circleSet karlssonOEISQ2.center karlssonOEISQ2.radius := by
  unfold q2q3CircleRayNearPoint
  exact
    ray_point_mem_circle_of_quadratic
      (anchor := karlssonOEISQ3.anchor)
      (center := karlssonOEISQ2.center)
      (direction := karlssonOEISQ3.rayDirection)
      (radius := karlssonOEISQ2.radius)
      (dot := q2q3CircleRayDot)
      (constant := q2q3CircleRayConstant)
      rfl rfl q3_rayDirection_normSq
      q2q3CircleRayNearTime_quadratic

theorem q2q3CircleRayFarPoint_mem_q2_circle :
    q2q3CircleRayFarPoint ∈
      circleSet karlssonOEISQ2.center karlssonOEISQ2.radius := by
  unfold q2q3CircleRayFarPoint
  exact
    ray_point_mem_circle_of_quadratic
      (anchor := karlssonOEISQ3.anchor)
      (center := karlssonOEISQ2.center)
      (direction := karlssonOEISQ3.rayDirection)
      (radius := karlssonOEISQ2.radius)
      (dot := q2q3CircleRayDot)
      (constant := q2q3CircleRayConstant)
      rfl rfl q3_rayDirection_normSq
      q2q3CircleRayFarTime_quadratic

theorem q2q3CircleRayNearPoint_mem_q3_ray :
    q2q3CircleRayNearPoint ∈
      raySet karlssonOEISQ3.anchor karlssonOEISQ3.rayDirection := by
  exact ⟨q2q3CircleRayNearTime, q2q3CircleRayNearTime_nonneg, rfl⟩

theorem q2q3CircleRayFarPoint_mem_q3_ray :
    q2q3CircleRayFarPoint ∈
      raySet karlssonOEISQ3.anchor karlssonOEISQ3.rayDirection := by
  exact ⟨q2q3CircleRayFarTime, q2q3CircleRayFarTime_nonneg, rfl⟩

theorem q2q3CircleRayNearPoint_mem_euclideanCircleRaySet :
    toEuclideanR2 q2q3CircleRayNearPoint ∈
      euclideanCircleRaySet karlssonOEISQ2 karlssonOEISQ3 :=
  mem_euclideanCircleRaySet_of_mem_circleSet_of_mem_raySet
    q2q3CircleRayNearPoint_mem_q2_circle
    q2q3CircleRayNearPoint_mem_q3_ray

theorem q2q3CircleRayFarPoint_mem_euclideanCircleRaySet :
    toEuclideanR2 q2q3CircleRayFarPoint ∈
      euclideanCircleRaySet karlssonOEISQ2 karlssonOEISQ3 :=
  mem_euclideanCircleRaySet_of_mem_circleSet_of_mem_raySet
    q2q3CircleRayFarPoint_mem_q2_circle
    q2q3CircleRayFarPoint_mem_q3_ray

theorem q2q3CircleRayNearPoint_mem_base_pairIntersectionSet :
    q2q3CircleRayNearPoint ∈
      karlssonOEISBaseArrangement.pairIntersectionSet
        (2 : Fin 4) (3 : Fin 4) := by
  exact
    OEISSevenPoint.pair_mem_of_euclideanCircleRay
      (i := (2 : Fin 4)) (j := (3 : Fin 4))
      (p := q2q3CircleRayNearPoint)
      (by
        simpa [karlssonOEISBaseArrangement] using
          q2q3CircleRayNearPoint_mem_euclideanCircleRaySet)

theorem q2q3CircleRayFarPoint_mem_base_pairIntersectionSet :
    q2q3CircleRayFarPoint ∈
      karlssonOEISBaseArrangement.pairIntersectionSet
        (2 : Fin 4) (3 : Fin 4) := by
  exact
    OEISSevenPoint.pair_mem_of_euclideanCircleRay
      (i := (2 : Fin 4)) (j := (3 : Fin 4))
      (p := q2q3CircleRayFarPoint)
      (by
        simpa [karlssonOEISBaseArrangement] using
          q2q3CircleRayFarPoint_mem_euclideanCircleRaySet)

/-- Positive dot coefficient in the quadratic for
`ray(Q2) ∩ circle(Q3)`. -/
private abbrev q2q3RayCircleDot : ℝ :=
  -dot2 (karlssonOEISQ2.anchor - karlssonOEISQ3.center)
    karlssonOEISQ2.rayDirection

/-- Constant term in the quadratic for `ray(Q2) ∩ circle(Q3)`. -/
private abbrev q2q3RayCircleConstant : ℝ :=
  distSq2 karlssonOEISQ2.anchor karlssonOEISQ3.center -
    karlssonOEISQ3.radius ^ 2

/-- Discriminant for `ray(Q2) ∩ circle(Q3)`. -/
private abbrev q2q3RayCircleDiscriminant : ℝ :=
  q2q3RayCircleDot ^ 2 - q2q3RayCircleConstant

private theorem q2q3RayCircleDot_expanded :
    q2q3RayCircleDot =
      (100 : ℝ) *
          (Real.cos alpha * Real.cos beta -
            Real.sin alpha * Real.sin beta) +
        ((7 : ℝ) / 10) * Real.cos alpha +
        q2q3DeltaX * Real.sin alpha := by
  unfold q2q3RayCircleDot q2q3DeltaX dot2
  simp [karlssonOEISQ2, karlssonOEISQ3, EuclideanLollipop.fromAnchor,
    angleDirection, point2, q2_theta_cos, q2_theta_sin,
    q3_theta_cos, q3_theta_sin]
  ring

private theorem q2q3RayCircleConstant_expanded :
    q2q3RayCircleConstant =
      q2q3DeltaX ^ 2 - 200 * q2q3DeltaX * Real.sin beta +
        (49 : ℝ) / 100 + 140 * Real.cos beta := by
  unfold q2q3RayCircleConstant q2q3DeltaX distSq2 normSq2 dot2
  simp [karlssonOEISQ2, karlssonOEISQ3, EuclideanLollipop.fromAnchor,
    angleDirection, point2, q3_theta_cos, q3_theta_sin]
  ring_nf
  have htrig :
      Real.sin (Real.pi * (1 / 30 : ℝ)) ^ 2 +
          Real.cos (Real.pi * (1 / 30 : ℝ)) ^ 2 = 1 := by
    exact Real.sin_sq_add_cos_sq (Real.pi * (1 / 30 : ℝ))
  nlinarith [htrig]

private theorem q2q3RayCircleDot_gt_fifty :
    (50 : ℝ) < q2q3RayCircleDot := by
  rw [q2q3RayCircleDot_expanded]
  nlinarith [one_half_lt_cos_alpha_cos_beta_sub_sin_alpha_sin_beta,
    cos_alpha_pos, q2q3DeltaX_pos, sin_alpha_pos]

private theorem q2q3RayCircleDot_pos :
    0 < q2q3RayCircleDot := by
  nlinarith [q2q3RayCircleDot_gt_fifty]

private theorem q2q3RayCircleConstant_pos :
    0 < q2q3RayCircleConstant := by
  rw [q2q3RayCircleConstant_expanded]
  nlinarith [sq_nonneg q2q3DeltaX,
    q2q3_delta_mul_sin_beta_lt_fourteen_div_seventy_five,
    one_half_lt_cos_beta]

private theorem q2q3RayCircleConstant_lt_two_hundred :
    q2q3RayCircleConstant < (200 : ℝ) := by
  rw [q2q3RayCircleConstant_expanded]
  have hcos_le : Real.cos beta ≤ 1 := Real.cos_le_one beta
  nlinarith [q2q3DeltaX_sq_lt_one, hcos_le,
    q2q3DeltaX_pos, sin_beta_pos]

private theorem q2q3RayCircleDiscriminant_pos :
    0 < q2q3RayCircleDiscriminant := by
  unfold q2q3RayCircleDiscriminant
  nlinarith [q2q3RayCircleDot_gt_fifty,
    q2q3RayCircleConstant_lt_two_hundred]

private theorem q2q3RayCircleDiscriminant_nonneg :
    0 ≤ q2q3RayCircleDiscriminant :=
  q2q3RayCircleDiscriminant_pos.le

private theorem q2q3RayCircle_sqrt_le_dot :
    Real.sqrt q2q3RayCircleDiscriminant ≤ q2q3RayCircleDot := by
  rw [Real.sqrt_le_iff]
  exact ⟨q2q3RayCircleDot_pos.le, by
    unfold q2q3RayCircleDiscriminant
    nlinarith [q2q3RayCircleConstant_pos]⟩

/-- Near forward time along the `Q2` ray at which it hits the `Q3` circle. -/
noncomputable def q2q3RayCircleNearTime : ℝ :=
  q2q3RayCircleDot - Real.sqrt q2q3RayCircleDiscriminant

/-- Far forward time along the `Q2` ray at which it hits the `Q3` circle. -/
noncomputable def q2q3RayCircleFarTime : ℝ :=
  q2q3RayCircleDot + Real.sqrt q2q3RayCircleDiscriminant

/-- Near intersection of the `Q2` ray with `circle(Q3)`. -/
noncomputable def q2q3RayCircleNearPoint : R2 :=
  karlssonOEISQ2.anchor +
    q2q3RayCircleNearTime • karlssonOEISQ2.rayDirection

/-- Far intersection of the `Q2` ray with `circle(Q3)`. -/
noncomputable def q2q3RayCircleFarPoint : R2 :=
  karlssonOEISQ2.anchor +
    q2q3RayCircleFarTime • karlssonOEISQ2.rayDirection

theorem q2q3RayCircleNearTime_nonneg :
    0 ≤ q2q3RayCircleNearTime := by
  unfold q2q3RayCircleNearTime
  nlinarith [q2q3RayCircle_sqrt_le_dot]

theorem q2q3RayCircleFarTime_nonneg :
    0 ≤ q2q3RayCircleFarTime := by
  unfold q2q3RayCircleFarTime
  nlinarith [q2q3RayCircleDot_pos,
    Real.sqrt_nonneg q2q3RayCircleDiscriminant]

private theorem q2q3RayCircleNearTime_quadratic :
    q2q3RayCircleNearTime ^ 2 -
        2 * q2q3RayCircleDot * q2q3RayCircleNearTime +
        q2q3RayCircleConstant = 0 := by
  unfold q2q3RayCircleNearTime q2q3RayCircleDiscriminant
  have hsqrt_sq :
      (Real.sqrt
          (q2q3RayCircleDot ^ 2 - q2q3RayCircleConstant)) ^ 2 =
        q2q3RayCircleDot ^ 2 - q2q3RayCircleConstant := by
    rw [Real.sq_sqrt]
    simpa [q2q3RayCircleDiscriminant] using
      q2q3RayCircleDiscriminant_nonneg
  nlinarith [hsqrt_sq]

private theorem q2q3RayCircleFarTime_quadratic :
    q2q3RayCircleFarTime ^ 2 -
        2 * q2q3RayCircleDot * q2q3RayCircleFarTime +
        q2q3RayCircleConstant = 0 := by
  unfold q2q3RayCircleFarTime q2q3RayCircleDiscriminant
  have hsqrt_sq :
      (Real.sqrt
          (q2q3RayCircleDot ^ 2 - q2q3RayCircleConstant)) ^ 2 =
        q2q3RayCircleDot ^ 2 - q2q3RayCircleConstant := by
    rw [Real.sq_sqrt]
    simpa [q2q3RayCircleDiscriminant] using
      q2q3RayCircleDiscriminant_nonneg
  nlinarith [hsqrt_sq]

theorem q2q3RayCircleNearPoint_mem_q2_ray :
    q2q3RayCircleNearPoint ∈
      raySet karlssonOEISQ2.anchor karlssonOEISQ2.rayDirection := by
  exact ⟨q2q3RayCircleNearTime, q2q3RayCircleNearTime_nonneg, rfl⟩

theorem q2q3RayCircleFarPoint_mem_q2_ray :
    q2q3RayCircleFarPoint ∈
      raySet karlssonOEISQ2.anchor karlssonOEISQ2.rayDirection := by
  exact ⟨q2q3RayCircleFarTime, q2q3RayCircleFarTime_nonneg, rfl⟩

theorem q2q3RayCircleNearPoint_mem_q3_circle :
    q2q3RayCircleNearPoint ∈
      circleSet karlssonOEISQ3.center karlssonOEISQ3.radius := by
  unfold q2q3RayCircleNearPoint
  exact
    ray_point_mem_circle_of_quadratic
      (anchor := karlssonOEISQ2.anchor)
      (center := karlssonOEISQ3.center)
      (direction := karlssonOEISQ2.rayDirection)
      (radius := karlssonOEISQ3.radius)
      (dot := q2q3RayCircleDot)
      (constant := q2q3RayCircleConstant)
      rfl rfl q2_rayDirection_normSq
      q2q3RayCircleNearTime_quadratic

theorem q2q3RayCircleFarPoint_mem_q3_circle :
    q2q3RayCircleFarPoint ∈
      circleSet karlssonOEISQ3.center karlssonOEISQ3.radius := by
  unfold q2q3RayCircleFarPoint
  exact
    ray_point_mem_circle_of_quadratic
      (anchor := karlssonOEISQ2.anchor)
      (center := karlssonOEISQ3.center)
      (direction := karlssonOEISQ2.rayDirection)
      (radius := karlssonOEISQ3.radius)
      (dot := q2q3RayCircleDot)
      (constant := q2q3RayCircleConstant)
      rfl rfl q2_rayDirection_normSq
      q2q3RayCircleFarTime_quadratic

theorem q2q3RayCircleNearPoint_mem_euclideanRayCircleSet :
    toEuclideanR2 q2q3RayCircleNearPoint ∈
      euclideanRayCircleSet karlssonOEISQ2 karlssonOEISQ3 :=
  mem_euclideanRayCircleSet_of_mem_raySet_of_mem_circleSet
    q2q3RayCircleNearPoint_mem_q2_ray
    q2q3RayCircleNearPoint_mem_q3_circle

theorem q2q3RayCircleFarPoint_mem_euclideanRayCircleSet :
    toEuclideanR2 q2q3RayCircleFarPoint ∈
      euclideanRayCircleSet karlssonOEISQ2 karlssonOEISQ3 :=
  mem_euclideanRayCircleSet_of_mem_raySet_of_mem_circleSet
    q2q3RayCircleFarPoint_mem_q2_ray
    q2q3RayCircleFarPoint_mem_q3_circle

theorem q2q3RayCircleNearPoint_mem_base_pairIntersectionSet :
    q2q3RayCircleNearPoint ∈
      karlssonOEISBaseArrangement.pairIntersectionSet
        (2 : Fin 4) (3 : Fin 4) := by
  exact
    OEISSevenPoint.pair_mem_of_euclideanRayCircle
      (i := (2 : Fin 4)) (j := (3 : Fin 4))
      (p := q2q3RayCircleNearPoint)
      (by
        simpa [karlssonOEISBaseArrangement] using
          q2q3RayCircleNearPoint_mem_euclideanRayCircleSet)

theorem q2q3RayCircleFarPoint_mem_base_pairIntersectionSet :
    q2q3RayCircleFarPoint ∈
      karlssonOEISBaseArrangement.pairIntersectionSet
        (2 : Fin 4) (3 : Fin 4) := by
  exact
    OEISSevenPoint.pair_mem_of_euclideanRayCircle
      (i := (2 : Fin 4)) (j := (3 : Fin 4))
      (p := q2q3RayCircleFarPoint)
      (by
        simpa [karlssonOEISBaseArrangement] using
          q2q3RayCircleFarPoint_mem_euclideanRayCircleSet)

/-- The `x`-coordinate of the center of `Q2`. -/
private abbrev q2q3Q2CenterX : ℝ :=
  (23 : ℝ) / 20 + 100 * Real.sin alpha

/-- The `y`-coordinate of the center of `Q2`. -/
private abbrev q2q3Q2CenterY : ℝ :=
  (13 : ℝ) / 20 + 100 * Real.cos alpha

/-- The `x`-coordinate of the center of `Q3`. -/
private abbrev q2q3Q3CenterX : ℝ :=
  karlssonOEISQ3AnchorX + 100 * Real.sin beta

/-- The `y`-coordinate of the center of `Q3`. -/
private abbrev q2q3Q3CenterY : ℝ :=
  -((1 : ℝ) / 20) - 100 * Real.cos beta

private theorem q2q3_q2_center_eq :
    karlssonOEISQ2.center =
      point2 q2q3Q2CenterX q2q3Q2CenterY := by
  ext i
  fin_cases i <;>
    simp [karlssonOEISQ2, EuclideanLollipop.fromAnchor, angleDirection,
      point2, q2q3Q2CenterX, q2q3Q2CenterY, q2_theta_cos,
      q2_theta_sin] <;> norm_num

private theorem q2q3_q3_center_eq :
    karlssonOEISQ3.center =
      point2 q2q3Q3CenterX q2q3Q3CenterY := by
  ext i
  fin_cases i <;>
    simp [karlssonOEISQ3, EuclideanLollipop.fromAnchor, angleDirection,
      point2, q2q3Q3CenterX, q2q3Q3CenterY, q3_theta_cos,
      q3_theta_sin]; norm_num

/-- Center displacement from `Q2`'s circle center to `Q3`'s circle center,
x-coordinate. -/
private abbrev q2q3CircleCircleDX : ℝ :=
  q2q3Q3CenterX - q2q3Q2CenterX

/-- Center displacement from `Q2`'s circle center to `Q3`'s circle center,
y-coordinate. -/
private abbrev q2q3CircleCircleDY : ℝ :=
  q2q3Q3CenterY - q2q3Q2CenterY

/-- Squared distance between the two circle centers for `(Q2,Q3)`. -/
private abbrev q2q3CircleCircleD : ℝ :=
  q2q3CircleCircleDX ^ 2 + q2q3CircleCircleDY ^ 2

/-- Radical-axis dot coordinate for the two equal-radius circle intersections. -/
private abbrev q2q3CircleCircleA : ℝ :=
  q2q3CircleCircleD / 2

/-- Squared perpendicular height of the two circle-circle intersections. -/
private abbrev q2q3CircleCircleH2 : ℝ :=
  (100 : ℝ) ^ 2 * q2q3CircleCircleD -
    q2q3CircleCircleA ^ 2

private theorem q2q3CircleCircleD_expanded :
    q2q3CircleCircleD =
      q2q3DeltaX ^ 2 +
        200 * q2q3DeltaX * (Real.sin alpha - Real.sin beta) +
        (49 : ℝ) / 100 +
        140 * (Real.cos alpha + Real.cos beta) +
        (10000 : ℝ) *
          (2 + 2 *
            (Real.cos alpha * Real.cos beta -
              Real.sin alpha * Real.sin beta)) := by
  unfold q2q3CircleCircleD q2q3CircleCircleDX q2q3CircleCircleDY
    q2q3Q2CenterX q2q3Q2CenterY q2q3Q3CenterX q2q3Q3CenterY
    q2q3DeltaX
  ring_nf
  have halpha :
      Real.sin alpha ^ 2 + Real.cos alpha ^ 2 = 1 :=
    Real.sin_sq_add_cos_sq alpha
  have hbeta :
      Real.sin beta ^ 2 + Real.cos beta ^ 2 = 1 :=
    Real.sin_sq_add_cos_sq beta
  dsimp [alpha, beta] at halpha hbeta
  ring_nf at halpha hbeta
  nlinarith [halpha, hbeta]

private theorem q2q3_sin_alpha_sub_sin_beta_lt_one :
    Real.sin alpha - Real.sin beta < 1 := by
  nlinarith [Real.sin_le_one alpha, sin_beta_pos]

private theorem q2q3_delta_mul_sin_alpha_sub_sin_beta_lt_fourteen_div_seventy_five :
    q2q3DeltaX * (Real.sin alpha - Real.sin beta) < (14 : ℝ) / 75 := by
  have hmul :
      q2q3DeltaX * (Real.sin alpha - Real.sin beta) <
        q2q3DeltaX * 1 :=
    mul_lt_mul_of_pos_left
      q2q3_sin_alpha_sub_sin_beta_lt_one q2q3DeltaX_pos
  nlinarith [hmul, q2q3DeltaX_lt_fourteen_div_seventy_five]

private theorem q2q3CircleCircleDY_lt_neg_hundred :
    q2q3CircleCircleDY < -(100 : ℝ) := by
  unfold q2q3CircleCircleDY q2q3Q2CenterY q2q3Q3CenterY
  nlinarith [one_half_lt_cos_alpha, one_half_lt_cos_beta]

private theorem q2q3CircleCircleD_gt_ten_thousand :
    (10000 : ℝ) < q2q3CircleCircleD := by
  unfold q2q3CircleCircleD
  nlinarith [q2q3CircleCircleDY_lt_neg_hundred,
    sq_nonneg q2q3CircleCircleDX]

private theorem q2q3CircleCircleD_gt_twenty_thousand :
    (20000 : ℝ) < q2q3CircleCircleD := by
  unfold q2q3CircleCircleD q2q3CircleCircleDY q2q3Q2CenterY
    q2q3Q3CenterY
  nlinarith [nine_div_ten_lt_cos_alpha, nine_div_ten_lt_cos_beta,
    sq_nonneg q2q3CircleCircleDX]

private theorem q2q3CircleCircleD_pos :
    0 < q2q3CircleCircleD := by
  nlinarith [q2q3CircleCircleD_gt_ten_thousand]

private theorem q2q3CircleCircleD_ne :
    q2q3CircleCircleD ≠ 0 :=
  q2q3CircleCircleD_pos.ne'

private theorem q2q3CircleCircleD_lt_forty_thousand :
    q2q3CircleCircleD < (40000 : ℝ) := by
  rw [q2q3CircleCircleD_expanded]
  have hcos_sum : Real.cos alpha + Real.cos beta ≤ 2 := by
    nlinarith [Real.cos_le_one alpha, Real.cos_le_one beta]
  nlinarith [q2q3DeltaX_sq_lt_one,
    q2q3_delta_mul_sin_alpha_sub_sin_beta_lt_fourteen_div_seventy_five,
    hcos_sum,
    cos_alpha_cos_beta_sub_sin_alpha_sin_beta_lt_nine_div_ten]

/-- The private center-distance abbreviation is exactly the squared distance
between the `Q2` and `Q3` circle centers. -/
theorem q2q3CircleCircleD_eq_distSq2_centers :
    q2q3CircleCircleD =
      distSq2 karlssonOEISQ2.center karlssonOEISQ3.center := by
  rw [q2q3_q2_center_eq, q2q3_q3_center_eq]
  simp [q2q3CircleCircleD, q2q3CircleCircleDX, q2q3CircleCircleDY,
    q2q3Q2CenterX, q2q3Q2CenterY, q2q3Q3CenterX, q2q3Q3CenterY,
    distSq2, normSq2, dot2, point2]
  ring

/-- The `Q2,Q3` circle pair satisfies Paulsen's strict obtuse-intersection
distance condition, hence is not intriguing. -/
theorem q2q3_circleObtuseCondition :
    TheoremOneEndToEnd.PaulsenLinearAlgebra.circleObtuseCondition
      karlssonOEISQ2.radius karlssonOEISQ3.radius
      karlssonOEISQ2.center karlssonOEISQ3.center := by
  unfold TheoremOneEndToEnd.PaulsenLinearAlgebra.circleObtuseCondition
  constructor
  · rw [← q2q3CircleCircleD_eq_distSq2_centers]
    have hrad :
        karlssonOEISQ2.radius ^ 2 + karlssonOEISQ3.radius ^ 2 =
          (20000 : ℝ) := by
      norm_num [karlssonOEISQ2, karlssonOEISQ3,
        EuclideanLollipop.fromAnchor]
    rw [hrad]
    exact q2q3CircleCircleD_gt_twenty_thousand
  · rw [← q2q3CircleCircleD_eq_distSq2_centers]
    have hsum :
        (karlssonOEISQ2.radius + karlssonOEISQ3.radius) ^ 2 =
          (40000 : ℝ) := by
      norm_num [karlssonOEISQ2, karlssonOEISQ3,
        EuclideanLollipop.fromAnchor]
    rw [hsum]
    exact q2q3CircleCircleD_lt_forty_thousand

/-- Pair-level form: `(Q2,Q3)` is not intriguing. -/
theorem q2q3_not_circleIntriguingPair :
    ¬ TheoremOneEndToEnd.PaulsenLinearAlgebra.circleIntriguingPair
      karlssonOEISQ2.radius karlssonOEISQ3.radius
      karlssonOEISQ2.center karlssonOEISQ3.center := by
  classical
  exact not_not.mpr q2q3_circleObtuseCondition

private theorem q2q3CircleCircleH2_pos :
    0 < q2q3CircleCircleH2 := by
  unfold q2q3CircleCircleH2 q2q3CircleCircleA
  have hprod :
      0 < q2q3CircleCircleD *
        ((40000 : ℝ) - q2q3CircleCircleD) :=
    mul_pos q2q3CircleCircleD_pos
      (sub_pos.2 q2q3CircleCircleD_lt_forty_thousand)
  nlinarith [hprod]

private theorem q2q3CircleCircleH2_nonneg :
    0 ≤ q2q3CircleCircleH2 :=
  q2q3CircleCircleH2_pos.le

/-- One of the two intersections of `circle(Q2)` and `circle(Q3)`. -/
noncomputable def q2q3CircleCircleUpperPoint : R2 :=
  point2
    (q2q3Q2CenterX +
      (q2q3CircleCircleA * q2q3CircleCircleDX -
        Real.sqrt q2q3CircleCircleH2 * q2q3CircleCircleDY) /
        q2q3CircleCircleD)
    (q2q3Q2CenterY +
      (q2q3CircleCircleA * q2q3CircleCircleDY +
        Real.sqrt q2q3CircleCircleH2 * q2q3CircleCircleDX) /
        q2q3CircleCircleD)

/-- The other intersection of `circle(Q2)` and `circle(Q3)`. -/
noncomputable def q2q3CircleCircleLowerPoint : R2 :=
  point2
    (q2q3Q2CenterX +
      (q2q3CircleCircleA * q2q3CircleCircleDX +
        Real.sqrt q2q3CircleCircleH2 * q2q3CircleCircleDY) /
        q2q3CircleCircleD)
    (q2q3Q2CenterY +
      (q2q3CircleCircleA * q2q3CircleCircleDY -
        Real.sqrt q2q3CircleCircleH2 * q2q3CircleCircleDX) /
        q2q3CircleCircleD)

private theorem q2q3CircleCircle_sqrt_sq :
    (Real.sqrt q2q3CircleCircleH2) ^ 2 =
      q2q3CircleCircleH2 :=
  Real.sq_sqrt q2q3CircleCircleH2_nonneg

private theorem q2q3CircleCircle_A_sq_add_H_sq :
    q2q3CircleCircleA ^ 2 +
        (Real.sqrt q2q3CircleCircleH2) ^ 2 =
      (100 : ℝ) ^ 2 * q2q3CircleCircleD := by
  rw [q2q3CircleCircle_sqrt_sq]
  unfold q2q3CircleCircleH2
  ring

private theorem q2q3CircleCircle_A_sub_D_sq_add_H_sq :
    (q2q3CircleCircleA - q2q3CircleCircleD) ^ 2 +
        (Real.sqrt q2q3CircleCircleH2) ^ 2 =
      (100 : ℝ) ^ 2 * q2q3CircleCircleD := by
  rw [q2q3CircleCircle_sqrt_sq]
  unfold q2q3CircleCircleH2 q2q3CircleCircleA
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

private theorem q2q3CircleCircleUpper_q2_coordinate :
    ((q2q3CircleCircleA * q2q3CircleCircleDX -
          Real.sqrt q2q3CircleCircleH2 * q2q3CircleCircleDY) /
        q2q3CircleCircleD) *
        ((q2q3CircleCircleA * q2q3CircleCircleDX -
            Real.sqrt q2q3CircleCircleH2 * q2q3CircleCircleDY) /
          q2q3CircleCircleD) +
      ((q2q3CircleCircleA * q2q3CircleCircleDY +
          Real.sqrt q2q3CircleCircleH2 * q2q3CircleCircleDX) /
        q2q3CircleCircleD) *
        ((q2q3CircleCircleA * q2q3CircleCircleDY +
            Real.sqrt q2q3CircleCircleH2 * q2q3CircleCircleDX) /
          q2q3CircleCircleD) =
      (100 : ℝ) ^ 2 := by
  exact circleCircleUpper_left_algebra
    q2q3CircleCircleDX q2q3CircleCircleDY q2q3CircleCircleD
    q2q3CircleCircleA (Real.sqrt q2q3CircleCircleH2) 100
    rfl q2q3CircleCircle_A_sq_add_H_sq q2q3CircleCircleD_ne

private theorem q2q3CircleCircleLower_q2_coordinate :
    ((q2q3CircleCircleA * q2q3CircleCircleDX +
          Real.sqrt q2q3CircleCircleH2 * q2q3CircleCircleDY) /
        q2q3CircleCircleD) *
        ((q2q3CircleCircleA * q2q3CircleCircleDX +
            Real.sqrt q2q3CircleCircleH2 * q2q3CircleCircleDY) /
          q2q3CircleCircleD) +
      ((q2q3CircleCircleA * q2q3CircleCircleDY -
          Real.sqrt q2q3CircleCircleH2 * q2q3CircleCircleDX) /
        q2q3CircleCircleD) *
        ((q2q3CircleCircleA * q2q3CircleCircleDY -
            Real.sqrt q2q3CircleCircleH2 * q2q3CircleCircleDX) /
          q2q3CircleCircleD) =
      (100 : ℝ) ^ 2 := by
  exact circleCircleLower_left_algebra
    q2q3CircleCircleDX q2q3CircleCircleDY q2q3CircleCircleD
    q2q3CircleCircleA (Real.sqrt q2q3CircleCircleH2) 100
    rfl q2q3CircleCircle_A_sq_add_H_sq q2q3CircleCircleD_ne

private theorem q2q3CircleCircleUpper_q3_coordinate :
    (q2q3Q2CenterX +
          (q2q3CircleCircleA * q2q3CircleCircleDX -
              Real.sqrt q2q3CircleCircleH2 * q2q3CircleCircleDY) /
            q2q3CircleCircleD -
        q2q3Q3CenterX) *
        (q2q3Q2CenterX +
            (q2q3CircleCircleA * q2q3CircleCircleDX -
                Real.sqrt q2q3CircleCircleH2 * q2q3CircleCircleDY) /
              q2q3CircleCircleD -
          q2q3Q3CenterX) +
      (q2q3Q2CenterY +
            (q2q3CircleCircleA * q2q3CircleCircleDY +
                Real.sqrt q2q3CircleCircleH2 * q2q3CircleCircleDX) /
              q2q3CircleCircleD -
          q2q3Q3CenterY) *
        (q2q3Q2CenterY +
            (q2q3CircleCircleA * q2q3CircleCircleDY +
                Real.sqrt q2q3CircleCircleH2 * q2q3CircleCircleDX) /
              q2q3CircleCircleD -
          q2q3Q3CenterY) =
      (100 : ℝ) ^ 2 := by
  have h := circleCircleUpper_right_algebra
    q2q3CircleCircleDX q2q3CircleCircleDY q2q3CircleCircleD
    q2q3CircleCircleA (Real.sqrt q2q3CircleCircleH2) 100
    rfl q2q3CircleCircle_A_sub_D_sq_add_H_sq q2q3CircleCircleD_ne
  unfold q2q3CircleCircleDX q2q3CircleCircleDY at h
  convert h using 1; ring

private theorem q2q3CircleCircleLower_q3_coordinate :
    (q2q3Q2CenterX +
          (q2q3CircleCircleA * q2q3CircleCircleDX +
              Real.sqrt q2q3CircleCircleH2 * q2q3CircleCircleDY) /
            q2q3CircleCircleD -
        q2q3Q3CenterX) *
        (q2q3Q2CenterX +
            (q2q3CircleCircleA * q2q3CircleCircleDX +
                Real.sqrt q2q3CircleCircleH2 * q2q3CircleCircleDY) /
              q2q3CircleCircleD -
          q2q3Q3CenterX) +
      (q2q3Q2CenterY +
            (q2q3CircleCircleA * q2q3CircleCircleDY -
                Real.sqrt q2q3CircleCircleH2 * q2q3CircleCircleDX) /
              q2q3CircleCircleD -
          q2q3Q3CenterY) *
        (q2q3Q2CenterY +
            (q2q3CircleCircleA * q2q3CircleCircleDY -
                Real.sqrt q2q3CircleCircleH2 * q2q3CircleCircleDX) /
              q2q3CircleCircleD -
          q2q3Q3CenterY) =
      (100 : ℝ) ^ 2 := by
  have h := circleCircleLower_right_algebra
    q2q3CircleCircleDX q2q3CircleCircleDY q2q3CircleCircleD
    q2q3CircleCircleA (Real.sqrt q2q3CircleCircleH2) 100
    rfl q2q3CircleCircle_A_sub_D_sq_add_H_sq q2q3CircleCircleD_ne
  unfold q2q3CircleCircleDX q2q3CircleCircleDY at h
  convert h using 1; ring

theorem q2q3CircleCircleUpperPoint_mem_q2_circle :
    q2q3CircleCircleUpperPoint ∈
      circleSet karlssonOEISQ2.center karlssonOEISQ2.radius := by
  unfold q2q3CircleCircleUpperPoint circleSet distSq2 normSq2 dot2
  rw [q2q3_q2_center_eq]
  simp [karlssonOEISQ2, EuclideanLollipop.fromAnchor, point2]
  exact q2q3CircleCircleUpper_q2_coordinate

theorem q2q3CircleCircleLowerPoint_mem_q2_circle :
    q2q3CircleCircleLowerPoint ∈
      circleSet karlssonOEISQ2.center karlssonOEISQ2.radius := by
  unfold q2q3CircleCircleLowerPoint circleSet distSq2 normSq2 dot2
  rw [q2q3_q2_center_eq]
  simp [karlssonOEISQ2, EuclideanLollipop.fromAnchor, point2]
  exact q2q3CircleCircleLower_q2_coordinate

theorem q2q3CircleCircleUpperPoint_mem_q3_circle :
    q2q3CircleCircleUpperPoint ∈
      circleSet karlssonOEISQ3.center karlssonOEISQ3.radius := by
  unfold q2q3CircleCircleUpperPoint circleSet distSq2 normSq2 dot2
  rw [q2q3_q3_center_eq]
  simp [karlssonOEISQ3, EuclideanLollipop.fromAnchor, point2]
  exact q2q3CircleCircleUpper_q3_coordinate

theorem q2q3CircleCircleLowerPoint_mem_q3_circle :
    q2q3CircleCircleLowerPoint ∈
      circleSet karlssonOEISQ3.center karlssonOEISQ3.radius := by
  unfold q2q3CircleCircleLowerPoint circleSet distSq2 normSq2 dot2
  rw [q2q3_q3_center_eq]
  simp [karlssonOEISQ3, EuclideanLollipop.fromAnchor, point2]
  exact q2q3CircleCircleLower_q3_coordinate

theorem q2q3CircleCircleUpperPoint_mem_euclideanCircleCircleSet :
    toEuclideanR2 q2q3CircleCircleUpperPoint ∈
      euclideanCircleCircleSet karlssonOEISQ2 karlssonOEISQ3 :=
  mem_euclideanCircleCircleSet_of_mem_circleSets
    q2q3CircleCircleUpperPoint_mem_q2_circle
    q2q3CircleCircleUpperPoint_mem_q3_circle

theorem q2q3CircleCircleLowerPoint_mem_euclideanCircleCircleSet :
    toEuclideanR2 q2q3CircleCircleLowerPoint ∈
      euclideanCircleCircleSet karlssonOEISQ2 karlssonOEISQ3 :=
  mem_euclideanCircleCircleSet_of_mem_circleSets
    q2q3CircleCircleLowerPoint_mem_q2_circle
    q2q3CircleCircleLowerPoint_mem_q3_circle

theorem q2q3CircleCircleUpperPoint_mem_base_pairIntersectionSet :
    q2q3CircleCircleUpperPoint ∈
      karlssonOEISBaseArrangement.pairIntersectionSet
        (2 : Fin 4) (3 : Fin 4) := by
  exact
    OEISSevenPoint.pair_mem_of_euclideanCircleCircle
      (i := (2 : Fin 4)) (j := (3 : Fin 4))
      (p := q2q3CircleCircleUpperPoint)
      (by
        simpa [karlssonOEISBaseArrangement] using
          q2q3CircleCircleUpperPoint_mem_euclideanCircleCircleSet)

theorem q2q3CircleCircleLowerPoint_mem_base_pairIntersectionSet :
    q2q3CircleCircleLowerPoint ∈
      karlssonOEISBaseArrangement.pairIntersectionSet
        (2 : Fin 4) (3 : Fin 4) := by
  exact
    OEISSevenPoint.pair_mem_of_euclideanCircleCircle
      (i := (2 : Fin 4)) (j := (3 : Fin 4))
      (p := q2q3CircleCircleLowerPoint)
      (by
        simpa [karlssonOEISBaseArrangement] using
          q2q3CircleCircleLowerPoint_mem_euclideanCircleCircleSet)

private theorem q2q3CircleRay_sqrt_lt_dot :
    Real.sqrt q2q3CircleRayDiscriminant < q2q3CircleRayDot := by
  rw [Real.sqrt_lt q2q3CircleRayDiscriminant_nonneg
    q2q3CircleRayDot_pos.le]
  unfold q2q3CircleRayDiscriminant
  nlinarith [q2q3CircleRayConstant_pos]

theorem q2q3CircleRayNearTime_pos :
    0 < q2q3CircleRayNearTime := by
  unfold q2q3CircleRayNearTime
  nlinarith [q2q3CircleRay_sqrt_lt_dot]

theorem q2q3CircleRayFarTime_pos :
    0 < q2q3CircleRayFarTime := by
  unfold q2q3CircleRayFarTime
  nlinarith [q2q3CircleRayDot_pos,
    Real.sqrt_nonneg q2q3CircleRayDiscriminant]

private theorem q2q3RayCircle_sqrt_lt_dot :
    Real.sqrt q2q3RayCircleDiscriminant < q2q3RayCircleDot := by
  rw [Real.sqrt_lt q2q3RayCircleDiscriminant_nonneg
    q2q3RayCircleDot_pos.le]
  unfold q2q3RayCircleDiscriminant
  nlinarith [q2q3RayCircleConstant_pos]

theorem q2q3RayCircleNearTime_pos :
    0 < q2q3RayCircleNearTime := by
  unfold q2q3RayCircleNearTime
  nlinarith [q2q3RayCircle_sqrt_lt_dot]

theorem q2q3RayCircleFarTime_pos :
    0 < q2q3RayCircleFarTime := by
  unfold q2q3RayCircleFarTime
  nlinarith [q2q3RayCircleDot_pos,
    Real.sqrt_nonneg q2q3RayCircleDiscriminant]

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
          Real.cos (Real.pi * (2 / 15 : ℝ)) ^ 2 = 1 := by
    exact Real.sin_sq_add_cos_sq (Real.pi * (2 / 15 : ℝ))
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
          Real.cos (Real.pi * (1 / 30 : ℝ)) ^ 2 = 1 := by
    exact Real.sin_sq_add_cos_sq (Real.pi * (1 / 30 : ℝ))
  nlinarith [htrig, ht, hp]

theorem q2q3CircleRayNearPoint_not_mem_q3_circle :
    q2q3CircleRayNearPoint ∉
      circleSet karlssonOEISQ3.center karlssonOEISQ3.radius := by
  unfold q2q3CircleRayNearPoint
  exact
    q3_ray_point_not_mem_q3_circle_of_time_pos
      q2q3CircleRayNearTime_pos

theorem q2q3CircleRayFarPoint_not_mem_q3_circle :
    q2q3CircleRayFarPoint ∉
      circleSet karlssonOEISQ3.center karlssonOEISQ3.radius := by
  unfold q2q3CircleRayFarPoint
  exact
    q3_ray_point_not_mem_q3_circle_of_time_pos
      q2q3CircleRayFarTime_pos

theorem q2q3RayCircleNearPoint_not_mem_q2_circle :
    q2q3RayCircleNearPoint ∉
      circleSet karlssonOEISQ2.center karlssonOEISQ2.radius := by
  unfold q2q3RayCircleNearPoint
  exact
    q2_ray_point_not_mem_q2_circle_of_time_pos
      q2q3RayCircleNearTime_pos

theorem q2q3RayCircleFarPoint_not_mem_q2_circle :
    q2q3RayCircleFarPoint ∉
      circleSet karlssonOEISQ2.center karlssonOEISQ2.radius := by
  unfold q2q3RayCircleFarPoint
  exact
    q2_ray_point_not_mem_q2_circle_of_time_pos
      q2q3RayCircleFarTime_pos

theorem q2q3RayRayPoint_not_mem_q2_circle :
    q2q3RayRayPoint ∉
      circleSet karlssonOEISQ2.center karlssonOEISQ2.radius := by
  unfold q2q3RayRayPoint
  exact
    q2_ray_point_not_mem_q2_circle_of_time_pos
      q2q3RayRayTimeQ2_pos

theorem q2q3RayRayPoint_not_mem_q3_circle :
    q2q3RayRayPoint ∉
      circleSet karlssonOEISQ3.center karlssonOEISQ3.radius := by
  intro hp
  exact
    (q3_ray_point_not_mem_q3_circle_of_time_pos
      q2q3RayRayTimeQ3_pos)
      (by
        simpa [q2q3RayRayPoint_eq_q3_ray_expression] using hp)

theorem q2q3CircleCircleUpperPoint_ne_lower :
    q2q3CircleCircleUpperPoint ≠ q2q3CircleCircleLowerPoint := by
  intro h
  have hx := congr_fun h 0
  unfold q2q3CircleCircleUpperPoint q2q3CircleCircleLowerPoint at hx
  simp [point2] at hx
  have hdiff :
      ((q2q3CircleCircleA * q2q3CircleCircleDX -
            Real.sqrt q2q3CircleCircleH2 * q2q3CircleCircleDY) /
          q2q3CircleCircleD) -
        ((q2q3CircleCircleA * q2q3CircleCircleDX +
            Real.sqrt q2q3CircleCircleH2 * q2q3CircleCircleDY) /
          q2q3CircleCircleD) = 0 := by
    exact sub_eq_zero.2 hx
  have hdiff_eval :
      ((q2q3CircleCircleA * q2q3CircleCircleDX -
            Real.sqrt q2q3CircleCircleH2 * q2q3CircleCircleDY) /
          q2q3CircleCircleD) -
        ((q2q3CircleCircleA * q2q3CircleCircleDX +
            Real.sqrt q2q3CircleCircleH2 * q2q3CircleCircleDY) /
          q2q3CircleCircleD) =
        (-2 * Real.sqrt q2q3CircleCircleH2 *
            q2q3CircleCircleDY) / q2q3CircleCircleD := by
    field_simp [q2q3CircleCircleD_ne]
    ring
  have hpos :
      0 <
        (-2 * Real.sqrt q2q3CircleCircleH2 *
            q2q3CircleCircleDY) / q2q3CircleCircleD := by
    have hH : 0 < Real.sqrt q2q3CircleCircleH2 :=
      Real.sqrt_pos.2 q2q3CircleCircleH2_pos
    have hnegDY : 0 < -q2q3CircleCircleDY := by
      nlinarith [q2q3CircleCircleDY_lt_neg_hundred]
    have hrewrite :
        (-2 * Real.sqrt q2q3CircleCircleH2 *
            q2q3CircleCircleDY) / q2q3CircleCircleD =
          (2 * Real.sqrt q2q3CircleCircleH2 *
              (-q2q3CircleCircleDY)) / q2q3CircleCircleD := by
      ring
    rw [hrewrite]
    exact div_pos (mul_pos (mul_pos (by norm_num) hH) hnegDY)
      q2q3CircleCircleD_pos
  rw [hdiff_eval] at hdiff
  nlinarith

theorem q2q3CircleRayNearPoint_ne_far :
    q2q3CircleRayNearPoint ≠ q2q3CircleRayFarPoint := by
  intro h
  have hy := congr_fun h 1
  unfold q2q3CircleRayNearPoint q2q3CircleRayFarPoint
    q2q3CircleRayNearTime q2q3CircleRayFarTime at hy
  simp [karlssonOEISQ3, EuclideanLollipop.fromAnchor, angleDirection,
    point2, q3_theta_sin] at hy
  have hsqrt : 0 < Real.sqrt q2q3CircleRayDiscriminant :=
    Real.sqrt_pos.2 q2q3CircleRayDiscriminant_pos
  rcases hy with htime | hcos
  · nlinarith [hsqrt, htime]
  · exact cos_beta_pos.ne' hcos

theorem q2q3RayCircleNearPoint_ne_far :
    q2q3RayCircleNearPoint ≠ q2q3RayCircleFarPoint := by
  intro h
  have hy := congr_fun h 1
  unfold q2q3RayCircleNearPoint q2q3RayCircleFarPoint
    q2q3RayCircleNearTime q2q3RayCircleFarTime at hy
  simp [karlssonOEISQ2, EuclideanLollipop.fromAnchor, angleDirection,
    point2, q2_theta_sin] at hy
  have hsqrt : 0 < Real.sqrt q2q3RayCircleDiscriminant :=
    Real.sqrt_pos.2 q2q3RayCircleDiscriminant_pos
  rcases hy with htime | hcos
  · nlinarith [hsqrt, htime]
  · exact cos_alpha_pos.ne' hcos

private theorem ne_of_left_mem_q2_circle_of_right_not_mem_q2_circle
    {p q : R2}
    (hp : p ∈ circleSet karlssonOEISQ2.center karlssonOEISQ2.radius)
    (hq : q ∉ circleSet karlssonOEISQ2.center karlssonOEISQ2.radius) :
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

theorem q2q3CircleCircleUpperPoint_ne_circleRayNear :
    q2q3CircleCircleUpperPoint ≠ q2q3CircleRayNearPoint :=
  ne_of_left_mem_q3_circle_of_right_not_mem_q3_circle
    q2q3CircleCircleUpperPoint_mem_q3_circle
    q2q3CircleRayNearPoint_not_mem_q3_circle

theorem q2q3CircleCircleUpperPoint_ne_circleRayFar :
    q2q3CircleCircleUpperPoint ≠ q2q3CircleRayFarPoint :=
  ne_of_left_mem_q3_circle_of_right_not_mem_q3_circle
    q2q3CircleCircleUpperPoint_mem_q3_circle
    q2q3CircleRayFarPoint_not_mem_q3_circle

theorem q2q3CircleCircleUpperPoint_ne_rayCircleNear :
    q2q3CircleCircleUpperPoint ≠ q2q3RayCircleNearPoint :=
  ne_of_left_mem_q2_circle_of_right_not_mem_q2_circle
    q2q3CircleCircleUpperPoint_mem_q2_circle
    q2q3RayCircleNearPoint_not_mem_q2_circle

theorem q2q3CircleCircleUpperPoint_ne_rayCircleFar :
    q2q3CircleCircleUpperPoint ≠ q2q3RayCircleFarPoint :=
  ne_of_left_mem_q2_circle_of_right_not_mem_q2_circle
    q2q3CircleCircleUpperPoint_mem_q2_circle
    q2q3RayCircleFarPoint_not_mem_q2_circle

theorem q2q3CircleCircleUpperPoint_ne_rayRay :
    q2q3CircleCircleUpperPoint ≠ q2q3RayRayPoint :=
  ne_of_left_mem_q3_circle_of_right_not_mem_q3_circle
    q2q3CircleCircleUpperPoint_mem_q3_circle
    q2q3RayRayPoint_not_mem_q3_circle

theorem q2q3CircleCircleLowerPoint_ne_circleRayNear :
    q2q3CircleCircleLowerPoint ≠ q2q3CircleRayNearPoint :=
  ne_of_left_mem_q3_circle_of_right_not_mem_q3_circle
    q2q3CircleCircleLowerPoint_mem_q3_circle
    q2q3CircleRayNearPoint_not_mem_q3_circle

theorem q2q3CircleCircleLowerPoint_ne_circleRayFar :
    q2q3CircleCircleLowerPoint ≠ q2q3CircleRayFarPoint :=
  ne_of_left_mem_q3_circle_of_right_not_mem_q3_circle
    q2q3CircleCircleLowerPoint_mem_q3_circle
    q2q3CircleRayFarPoint_not_mem_q3_circle

theorem q2q3CircleCircleLowerPoint_ne_rayCircleNear :
    q2q3CircleCircleLowerPoint ≠ q2q3RayCircleNearPoint :=
  ne_of_left_mem_q2_circle_of_right_not_mem_q2_circle
    q2q3CircleCircleLowerPoint_mem_q2_circle
    q2q3RayCircleNearPoint_not_mem_q2_circle

theorem q2q3CircleCircleLowerPoint_ne_rayCircleFar :
    q2q3CircleCircleLowerPoint ≠ q2q3RayCircleFarPoint :=
  ne_of_left_mem_q2_circle_of_right_not_mem_q2_circle
    q2q3CircleCircleLowerPoint_mem_q2_circle
    q2q3RayCircleFarPoint_not_mem_q2_circle

theorem q2q3CircleCircleLowerPoint_ne_rayRay :
    q2q3CircleCircleLowerPoint ≠ q2q3RayRayPoint :=
  ne_of_left_mem_q3_circle_of_right_not_mem_q3_circle
    q2q3CircleCircleLowerPoint_mem_q3_circle
    q2q3RayRayPoint_not_mem_q3_circle

theorem q2q3CircleRayNearPoint_ne_rayCircleNear :
    q2q3CircleRayNearPoint ≠ q2q3RayCircleNearPoint :=
  ne_of_left_mem_q2_circle_of_right_not_mem_q2_circle
    q2q3CircleRayNearPoint_mem_q2_circle
    q2q3RayCircleNearPoint_not_mem_q2_circle

theorem q2q3CircleRayNearPoint_ne_rayCircleFar :
    q2q3CircleRayNearPoint ≠ q2q3RayCircleFarPoint :=
  ne_of_left_mem_q2_circle_of_right_not_mem_q2_circle
    q2q3CircleRayNearPoint_mem_q2_circle
    q2q3RayCircleFarPoint_not_mem_q2_circle

theorem q2q3CircleRayNearPoint_ne_rayRay :
    q2q3CircleRayNearPoint ≠ q2q3RayRayPoint :=
  ne_of_left_mem_q2_circle_of_right_not_mem_q2_circle
    q2q3CircleRayNearPoint_mem_q2_circle
    q2q3RayRayPoint_not_mem_q2_circle

theorem q2q3CircleRayFarPoint_ne_rayCircleNear :
    q2q3CircleRayFarPoint ≠ q2q3RayCircleNearPoint :=
  ne_of_left_mem_q2_circle_of_right_not_mem_q2_circle
    q2q3CircleRayFarPoint_mem_q2_circle
    q2q3RayCircleNearPoint_not_mem_q2_circle

theorem q2q3CircleRayFarPoint_ne_rayCircleFar :
    q2q3CircleRayFarPoint ≠ q2q3RayCircleFarPoint :=
  ne_of_left_mem_q2_circle_of_right_not_mem_q2_circle
    q2q3CircleRayFarPoint_mem_q2_circle
    q2q3RayCircleFarPoint_not_mem_q2_circle

theorem q2q3CircleRayFarPoint_ne_rayRay :
    q2q3CircleRayFarPoint ≠ q2q3RayRayPoint :=
  ne_of_left_mem_q2_circle_of_right_not_mem_q2_circle
    q2q3CircleRayFarPoint_mem_q2_circle
    q2q3RayRayPoint_not_mem_q2_circle

theorem q2q3RayCircleNearPoint_ne_rayRay :
    q2q3RayCircleNearPoint ≠ q2q3RayRayPoint :=
  ne_of_left_mem_q3_circle_of_right_not_mem_q3_circle
    q2q3RayCircleNearPoint_mem_q3_circle
    q2q3RayRayPoint_not_mem_q3_circle

theorem q2q3RayCircleFarPoint_ne_rayRay :
    q2q3RayCircleFarPoint ≠ q2q3RayRayPoint :=
  ne_of_left_mem_q3_circle_of_right_not_mem_q3_circle
    q2q3RayCircleFarPoint_mem_q3_circle
    q2q3RayRayPoint_not_mem_q3_circle

/-- The seven explicit labelled component points for `(Q2,Q3)`. -/
noncomputable def q2q3SevenPointFinset : Finset R2 :=
  {q2q3CircleCircleUpperPoint, q2q3CircleCircleLowerPoint,
    q2q3CircleRayNearPoint, q2q3CircleRayFarPoint,
    q2q3RayCircleNearPoint, q2q3RayCircleFarPoint,
    q2q3RayRayPoint}

theorem q2q3SevenPointFinset_card :
    q2q3SevenPointFinset.card = 7 := by
  classical
  simp [q2q3SevenPointFinset,
    q2q3CircleCircleUpperPoint_ne_lower,
    q2q3CircleCircleUpperPoint_ne_circleRayNear,
    q2q3CircleCircleUpperPoint_ne_circleRayFar,
    q2q3CircleCircleUpperPoint_ne_rayCircleNear,
    q2q3CircleCircleUpperPoint_ne_rayCircleFar,
    q2q3CircleCircleUpperPoint_ne_rayRay,
    q2q3CircleCircleLowerPoint_ne_circleRayNear,
    q2q3CircleCircleLowerPoint_ne_circleRayFar,
    q2q3CircleCircleLowerPoint_ne_rayCircleNear,
    q2q3CircleCircleLowerPoint_ne_rayCircleFar,
    q2q3CircleCircleLowerPoint_ne_rayRay,
    q2q3CircleRayNearPoint_ne_far,
    q2q3CircleRayNearPoint_ne_rayCircleNear,
    q2q3CircleRayNearPoint_ne_rayCircleFar,
    q2q3CircleRayNearPoint_ne_rayRay,
    q2q3CircleRayFarPoint_ne_rayCircleNear,
    q2q3CircleRayFarPoint_ne_rayCircleFar,
    q2q3CircleRayFarPoint_ne_rayRay,
    q2q3RayCircleNearPoint_ne_far,
    q2q3RayCircleNearPoint_ne_rayRay,
    q2q3RayCircleFarPoint_ne_rayRay]

theorem q2q3SevenPointFinset_subset :
    ∀ p ∈ q2q3SevenPointFinset,
      p ∈ karlssonOEISBaseArrangement.pairIntersectionSet
        (2 : Fin 4) (3 : Fin 4) := by
  intro p hp
  simp [q2q3SevenPointFinset] at hp
  rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact q2q3CircleCircleUpperPoint_mem_base_pairIntersectionSet
  · exact q2q3CircleCircleLowerPoint_mem_base_pairIntersectionSet
  · exact q2q3CircleRayNearPoint_mem_base_pairIntersectionSet
  · exact q2q3CircleRayFarPoint_mem_base_pairIntersectionSet
  · exact q2q3RayCircleNearPoint_mem_base_pairIntersectionSet
  · exact q2q3RayCircleFarPoint_mem_base_pairIntersectionSet
  · exact q2q3RayRayPoint_mem_base_pairIntersectionSet

/-- Seven-point lower witness for the exact OEIS base pair `(Q2,Q3)`. -/
noncomputable def q2q3SevenPointSubset :
    OEISSevenPoint.SevenPointSubset (2 : Fin 4) (3 : Fin 4) where
  points := q2q3SevenPointFinset
  card_eq_seven := q2q3SevenPointFinset_card
  points_subset := q2q3SevenPointFinset_subset

/-- Exact pair-coordinate crossing certificate for `(Q2,Q3)`. -/
noncomputable def q2q3PairCoordinateCrossingCertificate :
    KarlssonOEISBasePairCoordinateCrossingCertificate
      (2 : Fin 4) (3 : Fin 4) (by decide) :=
  OEISSevenPoint.pair23Certificate q2q3SevenPointSubset

end

end OEISPair23
end CompleteFormalization
end TheoremOneManuscript
end Lollipop
