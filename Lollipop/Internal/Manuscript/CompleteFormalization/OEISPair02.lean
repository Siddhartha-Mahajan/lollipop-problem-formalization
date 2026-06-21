import Lollipop.Internal.Manuscript.CompleteFormalization.OEISSevenPoint
import Mathlib.Analysis.Real.Sqrt
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds

/-!
Concrete component witnesses for the OEIS/Karlsson base pair `(Q0,Q2)`.

This file completes the non-exceptional exact `= 7` work for `(Q0,Q2)` by
constructing the full seven-component witness used by the
`SevenComponentWitness` interface from `OEISSevenPoint.lean`.
-/

namespace Lollipop
namespace TheoremOneManuscript
namespace CompleteFormalization

open PrimitiveGeometry

namespace OEISPair02

noncomputable section

open ExplicitInputs
open TheoremOneEndToEnd.PaulsenLinearAlgebra (distSq2 normSq2 dot2)

private abbrev alpha : ℝ := 2 * Real.pi / 15

private theorem alpha_pos : 0 < alpha := by
  dsimp [alpha]
  nlinarith [Real.pi_pos]

private theorem alpha_lt_pi_div_four : alpha < Real.pi / 4 := by
  dsimp [alpha]
  nlinarith [Real.pi_pos]

private theorem alpha_lt_pi_div_two : alpha < Real.pi / 2 := by
  exact alpha_lt_pi_div_four.trans (by nlinarith [Real.pi_pos])

private theorem cos_alpha_pos : 0 < Real.cos alpha := by
  apply Real.cos_pos_of_mem_Ioo
  constructor
  · nlinarith [alpha_pos, Real.pi_pos]
  · exact alpha_lt_pi_div_two

private theorem sin_alpha_pos : 0 < Real.sin alpha := by
  apply Real.sin_pos_of_pos_of_lt_pi
  · exact alpha_pos
  · nlinarith [alpha_lt_pi_div_two, Real.pi_pos]

private theorem sin_alpha_lt_cos_alpha :
    Real.sin alpha < Real.cos alpha := by
  have h :
      Real.cos (Real.pi / 2 - alpha) < Real.cos alpha :=
    Real.cos_lt_cos_of_nonneg_of_le_pi_div_two
      alpha_pos.le
      (by nlinarith [alpha_pos])
      (by nlinarith [alpha_lt_pi_div_four])
  simpa [Real.cos_pi_div_two_sub] using h

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

/-- Forward time along the `Q2` ray until it hits the `Q0` ray's x-axis. -/
noncomputable def q0q2RayRayTime : ℝ :=
  ((65 : ℝ) / 100) / Real.cos alpha

/-- The concrete ray-ray point for the OEIS/Karlsson pair `(Q0,Q2)`. -/
noncomputable def q0q2RayRayPoint : R2 :=
  karlssonOEISQ2.anchor + q0q2RayRayTime • karlssonOEISQ2.rayDirection

theorem q0q2RayRayTime_pos : 0 < q0q2RayRayTime := by
  unfold q0q2RayRayTime
  exact div_pos (by norm_num) cos_alpha_pos

theorem q0q2RayRayPoint_y_eq_zero :
    q0q2RayRayPoint 1 = 0 := by
  have hcos_ne : Real.cos alpha ≠ 0 := cos_alpha_pos.ne'
  unfold q0q2RayRayPoint q0q2RayRayTime
  simp [karlssonOEISQ2, EuclideanLollipop.fromAnchor,
    angleDirection, point2, q2_theta_sin, alpha]
  field_simp [hcos_ne]
  ring

theorem q0q2RayRayPoint_x_pos :
    0 < q0q2RayRayPoint 0 := by
  have hcos_ne : Real.cos alpha ≠ 0 := cos_alpha_pos.ne'
  have htan_lt_one :
      Real.sin alpha / Real.cos alpha < 1 := by
    rw [div_lt_one cos_alpha_pos]
    exact sin_alpha_lt_cos_alpha
  have htan_lt_one' :
      Real.sin (2 * Real.pi / 15) / Real.cos (2 * Real.pi / 15) < 1 := by
    simpa [alpha] using htan_lt_one
  have hscaled :
      65 * Real.sin (2 * Real.pi / 15) /
          Real.cos (2 * Real.pi / 15) < 65 := by
    have hmul :=
      mul_lt_mul_of_pos_left htan_lt_one'
        (by norm_num : (0 : ℝ) < 65)
    simpa [mul_div_assoc] using hmul
  unfold q0q2RayRayPoint q0q2RayRayTime
  simp [karlssonOEISQ2, EuclideanLollipop.fromAnchor,
    angleDirection, point2, q2_theta_cos, alpha]
  field_simp [hcos_ne]
  nlinarith [hscaled]

theorem q0q2RayRayPoint_mem_q2_ray :
    q0q2RayRayPoint ∈
      raySet karlssonOEISQ2.anchor karlssonOEISQ2.rayDirection := by
  exact ⟨q0q2RayRayTime, q0q2RayRayTime_pos.le, rfl⟩

theorem q0q2RayRayPoint_mem_q0_ray :
    q0q2RayRayPoint ∈
      raySet karlssonOEISQ0.anchor karlssonOEISQ0.rayDirection := by
  refine ⟨q0q2RayRayPoint 0, q0q2RayRayPoint_x_pos.le, ?_⟩
  ext i
  fin_cases i
  · simp [karlssonOEISQ0, EuclideanLollipop.fromAnchor,
      angleDirection, point2]
  · simp [karlssonOEISQ0, EuclideanLollipop.fromAnchor,
      angleDirection, point2, q0q2RayRayPoint_y_eq_zero]

/-- Lifted ray-ray component form of the concrete `(Q0,Q2)` ray-ray point. -/
theorem q0q2RayRayPoint_mem_euclideanRayRaySet :
    toEuclideanR2 q0q2RayRayPoint ∈
      euclideanRayRaySet karlssonOEISQ0 karlssonOEISQ2 := by
  constructor
  · exact
      (mem_raySet_iff_mem_euclideanRaySet
        (p := q0q2RayRayPoint)
        (anchor := karlssonOEISQ0.anchor)
        (direction := karlssonOEISQ0.rayDirection)).1
        q0q2RayRayPoint_mem_q0_ray
  · exact
      (mem_raySet_iff_mem_euclideanRaySet
        (p := q0q2RayRayPoint)
        (anchor := karlssonOEISQ2.anchor)
        (direction := karlssonOEISQ2.rayDirection)).1
        q0q2RayRayPoint_mem_q2_ray

/-- Arrangement-indexed primitive carrier-intersection form. -/
theorem q0q2RayRayPoint_mem_base_pairIntersectionSet :
    q0q2RayRayPoint ∈
      karlssonOEISBaseArrangement.pairIntersectionSet
        (0 : Fin 4) (2 : Fin 4) := by
  exact
    OEISSevenPoint.pair_mem_of_euclideanRayRay
      (i := (0 : Fin 4)) (j := (2 : Fin 4))
      (p := q0q2RayRayPoint)
      (by
        simpa [karlssonOEISBaseArrangement] using
          q0q2RayRayPoint_mem_euclideanRayRaySet)

/-- The `x`-coordinate of the center of `Q2`, expressed in terms of
`alpha = 2π/15`. -/
private abbrev q0q2CenterX : ℝ :=
  (115 : ℝ) / 100 + 100 * Real.sin alpha

/-- The `y`-coordinate of the center of `Q2`, expressed in terms of
`alpha = 2π/15`. -/
private abbrev q0q2CenterY : ℝ :=
  (65 : ℝ) / 100 + 100 * Real.cos alpha

/-- The x-axis discriminant for `ray(Q0) ∩ circle(Q2)`. -/
private abbrev q0q2RayCircleDiscriminant : ℝ :=
  (100 : ℝ) ^ 2 - q0q2CenterY ^ 2

private theorem q0q2_q2_center_eq :
    karlssonOEISQ2.center = point2 q0q2CenterX q0q2CenterY := by
  ext i
  fin_cases i <;>
    simp [karlssonOEISQ2, EuclideanLollipop.fromAnchor, angleDirection,
      point2, q0q2CenterX, q0q2CenterY, q2_theta_cos, q2_theta_sin]

private theorem q0q2CenterX_pos : 0 < q0q2CenterX := by
  unfold q0q2CenterX
  nlinarith [sin_alpha_pos]

private theorem q0q2CenterY_pos : 0 < q0q2CenterY := by
  unfold q0q2CenterY
  nlinarith [cos_alpha_pos]

private theorem cos_alpha_le_two_seventeen_div_two_twenty_five :
    Real.cos alpha ≤ (217 : ℝ) / 225 := by
  have habs : |alpha| ≤ Real.pi := by
    rw [abs_of_nonneg alpha_pos.le]
    nlinarith [alpha_lt_pi_div_two, Real.pi_pos]
  calc
    Real.cos alpha ≤ 1 - 2 / Real.pi ^ 2 * alpha ^ 2 :=
      Real.cos_le_one_sub_mul_cos_sq habs
    _ = (217 : ℝ) / 225 := by
      dsimp [alpha]
      field_simp [Real.pi_pos.ne']
      ring

private theorem q0q2CenterY_lt_hundred : q0q2CenterY < 100 := by
  unfold q0q2CenterY
  nlinarith [cos_alpha_le_two_seventeen_div_two_twenty_five]

private theorem q0q2RayCircleDiscriminant_pos :
    0 < q0q2RayCircleDiscriminant := by
  unfold q0q2RayCircleDiscriminant
  have hprod :
      0 < (100 - q0q2CenterY) * (100 + q0q2CenterY) :=
    mul_pos (sub_pos.2 q0q2CenterY_lt_hundred)
      (by nlinarith [q0q2CenterY_pos])
  nlinarith [hprod]

private theorem q0q2RayCircleDiscriminant_nonneg :
    0 ≤ q0q2RayCircleDiscriminant :=
  q0q2RayCircleDiscriminant_pos.le

private theorem q0q2RayCircleDiscriminant_le_centerX_sq :
    q0q2RayCircleDiscriminant ≤ q0q2CenterX ^ 2 := by
  unfold q0q2RayCircleDiscriminant
  have hcenter_dist :
      (100 : ℝ) ^ 2 < q0q2CenterX ^ 2 + q0q2CenterY ^ 2 := by
    unfold q0q2CenterX q0q2CenterY
    nlinarith [Real.sin_sq_add_cos_sq alpha, sin_alpha_pos, cos_alpha_pos]
  nlinarith [hcenter_dist]

private theorem q0q2RayCircle_sqrt_le_centerX :
    Real.sqrt q0q2RayCircleDiscriminant ≤ q0q2CenterX := by
  rw [Real.sqrt_le_iff]
  exact ⟨q0q2CenterX_pos.le, q0q2RayCircleDiscriminant_le_centerX_sq⟩

/-- Left x-axis intersection of the `Q0` ray with the `Q2` circle. -/
noncomputable def q0q2RayCircleLeftPoint : R2 :=
  point2 (q0q2CenterX - Real.sqrt q0q2RayCircleDiscriminant) 0

/-- Right x-axis intersection of the `Q0` ray with the `Q2` circle. -/
noncomputable def q0q2RayCircleRightPoint : R2 :=
  point2 (q0q2CenterX + Real.sqrt q0q2RayCircleDiscriminant) 0

theorem q0q2RayCircleLeftPoint_x_nonneg :
    0 ≤ q0q2RayCircleLeftPoint 0 := by
  unfold q0q2RayCircleLeftPoint
  simp [point2]
  nlinarith [q0q2RayCircle_sqrt_le_centerX]

theorem q0q2RayCircleRightPoint_x_nonneg :
    0 ≤ q0q2RayCircleRightPoint 0 := by
  unfold q0q2RayCircleRightPoint
  simp [point2]
  nlinarith [q0q2CenterX_pos, Real.sqrt_nonneg q0q2RayCircleDiscriminant]

theorem q0q2RayCircleLeftPoint_mem_q0_ray :
    q0q2RayCircleLeftPoint ∈
      raySet karlssonOEISQ0.anchor karlssonOEISQ0.rayDirection := by
  refine ⟨q0q2RayCircleLeftPoint 0,
    q0q2RayCircleLeftPoint_x_nonneg, ?_⟩
  ext i
  fin_cases i <;>
    simp [q0q2RayCircleLeftPoint, karlssonOEISQ0,
      EuclideanLollipop.fromAnchor, angleDirection, point2]

theorem q0q2RayCircleRightPoint_mem_q0_ray :
    q0q2RayCircleRightPoint ∈
      raySet karlssonOEISQ0.anchor karlssonOEISQ0.rayDirection := by
  refine ⟨q0q2RayCircleRightPoint 0,
    q0q2RayCircleRightPoint_x_nonneg, ?_⟩
  ext i
  fin_cases i <;>
    simp [q0q2RayCircleRightPoint, karlssonOEISQ0,
      EuclideanLollipop.fromAnchor, angleDirection, point2]

theorem q0q2RayCircleLeftPoint_mem_q2_circle :
    q0q2RayCircleLeftPoint ∈
      circleSet karlssonOEISQ2.center karlssonOEISQ2.radius := by
  unfold q0q2RayCircleLeftPoint circleSet
    TheoremOneEndToEnd.PaulsenLinearAlgebra.distSq2
    TheoremOneEndToEnd.PaulsenLinearAlgebra.normSq2
    TheoremOneEndToEnd.PaulsenLinearAlgebra.dot2
  rw [q0q2_q2_center_eq]
  simp [point2, q0q2RayCircleDiscriminant]
  rw [Real.mul_self_sqrt
    (by
      simpa [q0q2RayCircleDiscriminant] using
        q0q2RayCircleDiscriminant_nonneg)]
  simp [karlssonOEISQ2, EuclideanLollipop.fromAnchor, q0q2CenterY]
  ring

theorem q0q2RayCircleRightPoint_mem_q2_circle :
    q0q2RayCircleRightPoint ∈
      circleSet karlssonOEISQ2.center karlssonOEISQ2.radius := by
  unfold q0q2RayCircleRightPoint circleSet
    TheoremOneEndToEnd.PaulsenLinearAlgebra.distSq2
    TheoremOneEndToEnd.PaulsenLinearAlgebra.normSq2
    TheoremOneEndToEnd.PaulsenLinearAlgebra.dot2
  rw [q0q2_q2_center_eq]
  simp [point2, q0q2RayCircleDiscriminant]
  rw [Real.mul_self_sqrt
    (by
      simpa [q0q2RayCircleDiscriminant] using
        q0q2RayCircleDiscriminant_nonneg)]
  simp [karlssonOEISQ2, EuclideanLollipop.fromAnchor, q0q2CenterY]
  ring

theorem q0q2RayCircleLeftPoint_mem_euclideanRayCircleSet :
    toEuclideanR2 q0q2RayCircleLeftPoint ∈
      euclideanRayCircleSet karlssonOEISQ0 karlssonOEISQ2 := by
  constructor
  · exact
      (mem_raySet_iff_mem_euclideanRaySet
        (p := q0q2RayCircleLeftPoint)
        (anchor := karlssonOEISQ0.anchor)
        (direction := karlssonOEISQ0.rayDirection)).1
        q0q2RayCircleLeftPoint_mem_q0_ray
  · exact
      (mem_circleSet_iff_mem_euclideanSphere
        karlssonOEISQ2.radius_pos.le).1
        q0q2RayCircleLeftPoint_mem_q2_circle

theorem q0q2RayCircleRightPoint_mem_euclideanRayCircleSet :
    toEuclideanR2 q0q2RayCircleRightPoint ∈
      euclideanRayCircleSet karlssonOEISQ0 karlssonOEISQ2 := by
  constructor
  · exact
      (mem_raySet_iff_mem_euclideanRaySet
        (p := q0q2RayCircleRightPoint)
        (anchor := karlssonOEISQ0.anchor)
        (direction := karlssonOEISQ0.rayDirection)).1
        q0q2RayCircleRightPoint_mem_q0_ray
  · exact
      (mem_circleSet_iff_mem_euclideanSphere
        karlssonOEISQ2.radius_pos.le).1
        q0q2RayCircleRightPoint_mem_q2_circle

theorem q0q2RayCircleLeftPoint_mem_base_pairIntersectionSet :
    q0q2RayCircleLeftPoint ∈
      karlssonOEISBaseArrangement.pairIntersectionSet
        (0 : Fin 4) (2 : Fin 4) := by
  exact
    OEISSevenPoint.pair_mem_of_euclideanRayCircle
      (i := (0 : Fin 4)) (j := (2 : Fin 4))
      (p := q0q2RayCircleLeftPoint)
      (by
        simpa [karlssonOEISBaseArrangement] using
          q0q2RayCircleLeftPoint_mem_euclideanRayCircleSet)

theorem q0q2RayCircleRightPoint_mem_base_pairIntersectionSet :
    q0q2RayCircleRightPoint ∈
      karlssonOEISBaseArrangement.pairIntersectionSet
        (0 : Fin 4) (2 : Fin 4) := by
  exact
    OEISSevenPoint.pair_mem_of_euclideanRayCircle
      (i := (0 : Fin 4)) (j := (2 : Fin 4))
      (p := q0q2RayCircleRightPoint)
      (by
        simpa [karlssonOEISBaseArrangement] using
          q0q2RayCircleRightPoint_mem_euclideanRayCircleSet)

/-- The positive dot coefficient in the quadratic for
`circle(Q0) ∩ ray(Q2)`. -/
private abbrev q0q2CircleRayDot : ℝ :=
  ((20115 : ℝ) / 100) * Real.sin alpha +
    ((65 : ℝ) / 100) * Real.cos alpha

/-- The constant term in the quadratic for `circle(Q0) ∩ ray(Q2)`. -/
private abbrev q0q2CircleRayConstant : ℝ :=
  ((20115 : ℝ) / 100) ^ 2 + ((65 : ℝ) / 100) ^ 2 -
    (200 : ℝ) ^ 2

/-- The discriminant for the two intersections of `circle(Q0)` with the
`Q2` ray. -/
private abbrev q0q2CircleRayDiscriminant : ℝ :=
  q0q2CircleRayDot ^ 2 - q0q2CircleRayConstant

private theorem four_div_fifteen_le_sin_alpha :
    (4 : ℝ) / 15 ≤ Real.sin alpha := by
  have h := Real.mul_le_sin alpha_pos.le alpha_lt_pi_div_two.le
  have hleft : 2 / Real.pi * alpha = (4 : ℝ) / 15 := by
    dsimp [alpha]
    field_simp [Real.pi_pos.ne']
    ring
  simpa [hleft] using h

private theorem q0q2CircleRayDot_ge_base :
    ((20115 : ℝ) / 100) * ((4 : ℝ) / 15) ≤ q0q2CircleRayDot := by
  unfold q0q2CircleRayDot
  nlinarith [four_div_fifteen_le_sin_alpha, cos_alpha_pos]

private theorem q0q2CircleRayDot_pos : 0 < q0q2CircleRayDot := by
  nlinarith [q0q2CircleRayDot_ge_base]

private theorem q0q2CircleRayConstant_pos :
    0 < q0q2CircleRayConstant := by
  norm_num [q0q2CircleRayConstant]

private theorem q0q2CircleRayDiscriminant_pos :
    0 < q0q2CircleRayDiscriminant := by
  unfold q0q2CircleRayDiscriminant
  have hbase :
      q0q2CircleRayConstant <
        (((20115 : ℝ) / 100) * ((4 : ℝ) / 15)) ^ 2 := by
    norm_num [q0q2CircleRayConstant]
  have hsq :
      (((20115 : ℝ) / 100) * ((4 : ℝ) / 15)) ^ 2 ≤
        q0q2CircleRayDot ^ 2 := by
    nlinarith [q0q2CircleRayDot_ge_base,
      sq_nonneg (q0q2CircleRayDot -
        ((20115 : ℝ) / 100) * ((4 : ℝ) / 15))]
  exact sub_pos.2 (hbase.trans_le hsq)

private theorem q0q2CircleRayDiscriminant_nonneg :
    0 ≤ q0q2CircleRayDiscriminant :=
  q0q2CircleRayDiscriminant_pos.le

private theorem q0q2CircleRay_sqrt_le_dot :
    Real.sqrt q0q2CircleRayDiscriminant ≤ q0q2CircleRayDot := by
  rw [Real.sqrt_le_iff]
  exact ⟨q0q2CircleRayDot_pos.le, by
    unfold q0q2CircleRayDiscriminant
    nlinarith [q0q2CircleRayConstant_pos]⟩

/-- Near forward time along the `Q2` ray at which it hits the `Q0` circle. -/
noncomputable def q0q2CircleRayNearTime : ℝ :=
  q0q2CircleRayDot - Real.sqrt q0q2CircleRayDiscriminant

/-- Far forward time along the `Q2` ray at which it hits the `Q0` circle. -/
noncomputable def q0q2CircleRayFarTime : ℝ :=
  q0q2CircleRayDot + Real.sqrt q0q2CircleRayDiscriminant

/-- Near intersection of `circle(Q0)` with the `Q2` ray. -/
noncomputable def q0q2CircleRayNearPoint : R2 :=
  karlssonOEISQ2.anchor +
    q0q2CircleRayNearTime • karlssonOEISQ2.rayDirection

/-- Far intersection of `circle(Q0)` with the `Q2` ray. -/
noncomputable def q0q2CircleRayFarPoint : R2 :=
  karlssonOEISQ2.anchor +
    q0q2CircleRayFarTime • karlssonOEISQ2.rayDirection

theorem q0q2CircleRayNearTime_nonneg :
    0 ≤ q0q2CircleRayNearTime := by
  unfold q0q2CircleRayNearTime
  nlinarith [q0q2CircleRay_sqrt_le_dot]

theorem q0q2CircleRayFarTime_nonneg :
    0 ≤ q0q2CircleRayFarTime := by
  unfold q0q2CircleRayFarTime
  nlinarith [q0q2CircleRayDot_pos,
    Real.sqrt_nonneg q0q2CircleRayDiscriminant]

private theorem q0q2CircleRayNearTime_quadratic :
    q0q2CircleRayNearTime ^ 2 -
        2 * q0q2CircleRayDot * q0q2CircleRayNearTime +
        q0q2CircleRayConstant = 0 := by
  unfold q0q2CircleRayNearTime q0q2CircleRayDiscriminant
  have hsqrt_sq :
      (Real.sqrt
          (q0q2CircleRayDot ^ 2 - q0q2CircleRayConstant)) ^ 2 =
        q0q2CircleRayDot ^ 2 - q0q2CircleRayConstant := by
    rw [Real.sq_sqrt]
    simpa [q0q2CircleRayDiscriminant] using
      q0q2CircleRayDiscriminant_nonneg
  nlinarith [hsqrt_sq]

private theorem q0q2CircleRayFarTime_quadratic :
    q0q2CircleRayFarTime ^ 2 -
        2 * q0q2CircleRayDot * q0q2CircleRayFarTime +
        q0q2CircleRayConstant = 0 := by
  unfold q0q2CircleRayFarTime q0q2CircleRayDiscriminant
  have hsqrt_sq :
      (Real.sqrt
          (q0q2CircleRayDot ^ 2 - q0q2CircleRayConstant)) ^ 2 =
        q0q2CircleRayDot ^ 2 - q0q2CircleRayConstant := by
    rw [Real.sq_sqrt]
    simpa [q0q2CircleRayDiscriminant] using
      q0q2CircleRayDiscriminant_nonneg
  nlinarith [hsqrt_sq]

private theorem q0q2CircleRayPoint_mem_q0_circle_of_quadratic
    {t : ℝ}
    (hquad :
      t ^ 2 - 2 * q0q2CircleRayDot * t +
          q0q2CircleRayConstant = 0) :
    karlssonOEISQ2.anchor + t • karlssonOEISQ2.rayDirection ∈
      circleSet karlssonOEISQ0.center karlssonOEISQ0.radius := by
  unfold q0q2CircleRayDot q0q2CircleRayConstant at hquad
  unfold circleSet
    TheoremOneEndToEnd.PaulsenLinearAlgebra.distSq2
    TheoremOneEndToEnd.PaulsenLinearAlgebra.normSq2
    TheoremOneEndToEnd.PaulsenLinearAlgebra.dot2
  simp [karlssonOEISQ0, karlssonOEISQ2, EuclideanLollipop.fromAnchor,
    angleDirection, point2, q2_theta_cos, q2_theta_sin]
  ring_nf at hquad ⊢
  have htrig :
      Real.sin (Real.pi * (2 / 15 : ℝ)) ^ 2 +
          Real.cos (Real.pi * (2 / 15 : ℝ)) ^ 2 = 1 := by
    exact Real.sin_sq_add_cos_sq (Real.pi * (2 / 15 : ℝ))
  nlinarith [htrig, hquad]

theorem q0q2CircleRayNearPoint_mem_q0_circle :
    q0q2CircleRayNearPoint ∈
      circleSet karlssonOEISQ0.center karlssonOEISQ0.radius := by
  unfold q0q2CircleRayNearPoint
  exact
    q0q2CircleRayPoint_mem_q0_circle_of_quadratic
      q0q2CircleRayNearTime_quadratic

theorem q0q2CircleRayFarPoint_mem_q0_circle :
    q0q2CircleRayFarPoint ∈
      circleSet karlssonOEISQ0.center karlssonOEISQ0.radius := by
  unfold q0q2CircleRayFarPoint
  exact
    q0q2CircleRayPoint_mem_q0_circle_of_quadratic
      q0q2CircleRayFarTime_quadratic

theorem q0q2CircleRayNearPoint_mem_q2_ray :
    q0q2CircleRayNearPoint ∈
      raySet karlssonOEISQ2.anchor karlssonOEISQ2.rayDirection := by
  exact ⟨q0q2CircleRayNearTime, q0q2CircleRayNearTime_nonneg, rfl⟩

theorem q0q2CircleRayFarPoint_mem_q2_ray :
    q0q2CircleRayFarPoint ∈
      raySet karlssonOEISQ2.anchor karlssonOEISQ2.rayDirection := by
  exact ⟨q0q2CircleRayFarTime, q0q2CircleRayFarTime_nonneg, rfl⟩

theorem q0q2CircleRayNearPoint_mem_euclideanCircleRaySet :
    toEuclideanR2 q0q2CircleRayNearPoint ∈
      euclideanCircleRaySet karlssonOEISQ0 karlssonOEISQ2 := by
  constructor
  · exact
      (mem_circleSet_iff_mem_euclideanSphere
        karlssonOEISQ0.radius_pos.le).1
        q0q2CircleRayNearPoint_mem_q0_circle
  · exact
      (mem_raySet_iff_mem_euclideanRaySet
        (p := q0q2CircleRayNearPoint)
        (anchor := karlssonOEISQ2.anchor)
        (direction := karlssonOEISQ2.rayDirection)).1
        q0q2CircleRayNearPoint_mem_q2_ray

theorem q0q2CircleRayFarPoint_mem_euclideanCircleRaySet :
    toEuclideanR2 q0q2CircleRayFarPoint ∈
      euclideanCircleRaySet karlssonOEISQ0 karlssonOEISQ2 := by
  constructor
  · exact
      (mem_circleSet_iff_mem_euclideanSphere
        karlssonOEISQ0.radius_pos.le).1
        q0q2CircleRayFarPoint_mem_q0_circle
  · exact
      (mem_raySet_iff_mem_euclideanRaySet
        (p := q0q2CircleRayFarPoint)
        (anchor := karlssonOEISQ2.anchor)
        (direction := karlssonOEISQ2.rayDirection)).1
        q0q2CircleRayFarPoint_mem_q2_ray

theorem q0q2CircleRayNearPoint_mem_base_pairIntersectionSet :
    q0q2CircleRayNearPoint ∈
      karlssonOEISBaseArrangement.pairIntersectionSet
        (0 : Fin 4) (2 : Fin 4) := by
  exact
    OEISSevenPoint.pair_mem_of_euclideanCircleRay
      (i := (0 : Fin 4)) (j := (2 : Fin 4))
      (p := q0q2CircleRayNearPoint)
      (by
        simpa [karlssonOEISBaseArrangement] using
          q0q2CircleRayNearPoint_mem_euclideanCircleRaySet)

theorem q0q2CircleRayFarPoint_mem_base_pairIntersectionSet :
    q0q2CircleRayFarPoint ∈
      karlssonOEISBaseArrangement.pairIntersectionSet
        (0 : Fin 4) (2 : Fin 4) := by
  exact
    OEISSevenPoint.pair_mem_of_euclideanCircleRay
      (i := (0 : Fin 4)) (j := (2 : Fin 4))
      (p := q0q2CircleRayFarPoint)
      (by
        simpa [karlssonOEISBaseArrangement] using
          q0q2CircleRayFarPoint_mem_euclideanCircleRaySet)

/-- Center displacement from `Q0`'s circle center to `Q2`'s circle center,
x-coordinate. -/
private abbrev q0q2CircleCircleDX : ℝ :=
  q0q2CenterX + 200

/-- Center displacement from `Q0`'s circle center to `Q2`'s circle center,
y-coordinate. -/
private abbrev q0q2CircleCircleDY : ℝ :=
  q0q2CenterY

/-- Squared distance between the two circle centers for `(Q0,Q2)`. -/
private abbrev q0q2CircleCircleD : ℝ :=
  q0q2CircleCircleDX ^ 2 + q0q2CircleCircleDY ^ 2

/-- Radical-axis dot coordinate for the two circle-circle intersections. -/
private abbrev q0q2CircleCircleA : ℝ :=
  (q0q2CircleCircleD + (30000 : ℝ)) / 2

/-- Squared perpendicular height of the two circle-circle intersections. -/
private abbrev q0q2CircleCircleH2 : ℝ :=
  (200 : ℝ) ^ 2 * q0q2CircleCircleD -
    q0q2CircleCircleA ^ 2

private theorem sin_alpha_le_eight_div_fifteen :
    Real.sin alpha ≤ (8 : ℝ) / 15 := by
  have hsin_le_alpha : Real.sin alpha ≤ alpha :=
    Real.sin_le alpha_pos.le
  have halpha_le : alpha ≤ (8 : ℝ) / 15 := by
    dsimp [alpha]
    nlinarith [Real.pi_le_four]
  exact hsin_le_alpha.trans halpha_le

private theorem q0q2CircleCircleDX_gt_hundred :
    (100 : ℝ) < q0q2CircleCircleDX := by
  unfold q0q2CircleCircleDX q0q2CenterX
  nlinarith [sin_alpha_pos]

private theorem q0q2CircleCircleD_pos :
    0 < q0q2CircleCircleD := by
  unfold q0q2CircleCircleD
  nlinarith [q0q2CircleCircleDX_gt_hundred,
    sq_nonneg q0q2CircleCircleDY]

private theorem q0q2CircleCircleD_ne :
    q0q2CircleCircleD ≠ 0 :=
  q0q2CircleCircleD_pos.ne'

private theorem q0q2CircleCircleD_gt_ten_thousand :
    (10000 : ℝ) < q0q2CircleCircleD := by
  unfold q0q2CircleCircleD
  nlinarith [q0q2CircleCircleDX_gt_hundred,
    sq_nonneg q0q2CircleCircleDY]

private theorem q0q2CircleCircleD_gt_fifty_thousand :
    (50000 : ℝ) < q0q2CircleCircleD := by
  unfold q0q2CircleCircleD q0q2CircleCircleDX q0q2CenterX
  nlinarith [four_div_fifteen_le_sin_alpha,
    sq_nonneg q0q2CircleCircleDY]

private theorem q0q2CircleCircleD_lt_ninety_thousand :
    q0q2CircleCircleD < (90000 : ℝ) := by
  unfold q0q2CircleCircleD q0q2CircleCircleDX q0q2CircleCircleDY
    q0q2CenterX q0q2CenterY
  nlinarith [Real.sin_sq_add_cos_sq alpha,
    sin_alpha_le_eight_div_fifteen, Real.cos_le_one alpha]

/-- The private center-distance abbreviation is exactly the squared distance
between the `Q0` and `Q2` circle centers. -/
theorem q0q2CircleCircleD_eq_distSq2_centers :
    q0q2CircleCircleD =
      distSq2 karlssonOEISQ0.center karlssonOEISQ2.center := by
  rw [q0q2_q2_center_eq]
  simp [q0q2CircleCircleD, q0q2CircleCircleDX, q0q2CircleCircleDY,
    q0q2CenterX, q0q2CenterY, karlssonOEISQ0,
    EuclideanLollipop.fromAnchor, distSq2, normSq2, dot2, point2]
  ring

/-- The `Q0,Q2` circle pair satisfies Paulsen's strict obtuse-intersection
distance condition, hence is not intriguing. -/
theorem q0q2_circleObtuseCondition :
    TheoremOneEndToEnd.PaulsenLinearAlgebra.circleObtuseCondition
      karlssonOEISQ0.radius karlssonOEISQ2.radius
      karlssonOEISQ0.center karlssonOEISQ2.center := by
  unfold TheoremOneEndToEnd.PaulsenLinearAlgebra.circleObtuseCondition
  constructor
  · rw [← q0q2CircleCircleD_eq_distSq2_centers]
    have hrad :
        karlssonOEISQ0.radius ^ 2 + karlssonOEISQ2.radius ^ 2 =
          (50000 : ℝ) := by
      norm_num [karlssonOEISQ0, karlssonOEISQ2,
        EuclideanLollipop.fromAnchor]
    rw [hrad]
    exact q0q2CircleCircleD_gt_fifty_thousand
  · rw [← q0q2CircleCircleD_eq_distSq2_centers]
    have hsum :
        (karlssonOEISQ0.radius + karlssonOEISQ2.radius) ^ 2 =
          (90000 : ℝ) := by
      norm_num [karlssonOEISQ0, karlssonOEISQ2,
        EuclideanLollipop.fromAnchor]
    rw [hsum]
    exact q0q2CircleCircleD_lt_ninety_thousand

/-- Pair-level form: `(Q0,Q2)` is not intriguing. -/
theorem q0q2_not_circleIntriguingPair :
    ¬ TheoremOneEndToEnd.PaulsenLinearAlgebra.circleIntriguingPair
      karlssonOEISQ0.radius karlssonOEISQ2.radius
      karlssonOEISQ0.center karlssonOEISQ2.center := by
  classical
  exact not_not.mpr q0q2_circleObtuseCondition

private theorem q0q2CircleCircleH2_pos :
    0 < q0q2CircleCircleH2 := by
  unfold q0q2CircleCircleH2 q0q2CircleCircleA
  have hprod :
      0 <
        ((90000 : ℝ) - q0q2CircleCircleD) *
          (q0q2CircleCircleD - (10000 : ℝ)) :=
    mul_pos (sub_pos.2 q0q2CircleCircleD_lt_ninety_thousand)
      (sub_pos.2 q0q2CircleCircleD_gt_ten_thousand)
  nlinarith [hprod]

private theorem q0q2CircleCircleH2_nonneg :
    0 ≤ q0q2CircleCircleH2 :=
  q0q2CircleCircleH2_pos.le

/-- One of the two intersections of `circle(Q0)` and `circle(Q2)`. -/
noncomputable def q0q2CircleCircleUpperPoint : R2 :=
  point2
    (-(200 : ℝ) +
      (q0q2CircleCircleA * q0q2CircleCircleDX -
        Real.sqrt q0q2CircleCircleH2 * q0q2CircleCircleDY) /
        q0q2CircleCircleD)
    ((q0q2CircleCircleA * q0q2CircleCircleDY +
        Real.sqrt q0q2CircleCircleH2 * q0q2CircleCircleDX) /
        q0q2CircleCircleD)

/-- The other intersection of `circle(Q0)` and `circle(Q2)`. -/
noncomputable def q0q2CircleCircleLowerPoint : R2 :=
  point2
    (-(200 : ℝ) +
      (q0q2CircleCircleA * q0q2CircleCircleDX +
        Real.sqrt q0q2CircleCircleH2 * q0q2CircleCircleDY) /
        q0q2CircleCircleD)
    ((q0q2CircleCircleA * q0q2CircleCircleDY -
        Real.sqrt q0q2CircleCircleH2 * q0q2CircleCircleDX) /
        q0q2CircleCircleD)

private theorem q0q2CircleCircle_sqrt_sq :
    (Real.sqrt q0q2CircleCircleH2) ^ 2 =
      q0q2CircleCircleH2 :=
  Real.sq_sqrt q0q2CircleCircleH2_nonneg

private theorem q0q2CircleCircle_A_sq_add_H_sq_q0 :
    q0q2CircleCircleA ^ 2 +
        (Real.sqrt q0q2CircleCircleH2) ^ 2 =
      (200 : ℝ) ^ 2 * q0q2CircleCircleD := by
  rw [q0q2CircleCircle_sqrt_sq]
  unfold q0q2CircleCircleH2
  ring

private theorem q0q2CircleCircle_A_sub_D_sq_add_H_sq_q2 :
    (q0q2CircleCircleA - q0q2CircleCircleD) ^ 2 +
        (Real.sqrt q0q2CircleCircleH2) ^ 2 =
      (100 : ℝ) ^ 2 * q0q2CircleCircleD := by
  rw [q0q2CircleCircle_sqrt_sq]
  unfold q0q2CircleCircleH2 q0q2CircleCircleA
  ring

private theorem circleCircleUpper_q0_algebra
    (dx dy D A H : ℝ)
    (hD : D = dx ^ 2 + dy ^ 2)
    (hAH : A ^ 2 + H ^ 2 = (200 : ℝ) ^ 2 * D)
    (hDne : D ≠ 0) :
    ((A * dx - H * dy) / D) * ((A * dx - H * dy) / D) +
      ((A * dy + H * dx) / D) * ((A * dy + H * dx) / D) =
      (200 : ℝ) ^ 2 := by
  field_simp [hDne]
  nlinarith [hD, hAH]

private theorem circleCircleLower_q0_algebra
    (dx dy D A H : ℝ)
    (hD : D = dx ^ 2 + dy ^ 2)
    (hAH : A ^ 2 + H ^ 2 = (200 : ℝ) ^ 2 * D)
    (hDne : D ≠ 0) :
    ((A * dx + H * dy) / D) * ((A * dx + H * dy) / D) +
      ((A * dy - H * dx) / D) * ((A * dy - H * dx) / D) =
      (200 : ℝ) ^ 2 := by
  field_simp [hDne]
  nlinarith [hD, hAH]

private theorem circleCircleUpper_q2_algebra
    (dx dy D A H cx cy : ℝ)
    (hD : D = dx ^ 2 + dy ^ 2)
    (hdx : dx = cx + 200)
    (hdy : dy = cy)
    (hAH : (A - D) ^ 2 + H ^ 2 = (100 : ℝ) ^ 2 * D)
    (hDne : D ≠ 0) :
    (-200 + (A * dx - H * dy) / D - cx) *
        (-200 + (A * dx - H * dy) / D - cx) +
      ((A * dy + H * dx) / D - cy) *
        ((A * dy + H * dx) / D - cy) =
      (100 : ℝ) ^ 2 := by
  subst dy
  subst dx
  field_simp [hDne]
  nlinarith [hD, hAH]

private theorem circleCircleLower_q2_algebra
    (dx dy D A H cx cy : ℝ)
    (hD : D = dx ^ 2 + dy ^ 2)
    (hdx : dx = cx + 200)
    (hdy : dy = cy)
    (hAH : (A - D) ^ 2 + H ^ 2 = (100 : ℝ) ^ 2 * D)
    (hDne : D ≠ 0) :
    (-200 + (A * dx + H * dy) / D - cx) *
        (-200 + (A * dx + H * dy) / D - cx) +
      ((A * dy - H * dx) / D - cy) *
        ((A * dy - H * dx) / D - cy) =
      (100 : ℝ) ^ 2 := by
  subst dy
  subst dx
  field_simp [hDne]
  nlinarith [hD, hAH]

private theorem q0q2CircleCircleUpper_q0_coordinate :
    ((q0q2CircleCircleA * q0q2CircleCircleDX -
          Real.sqrt q0q2CircleCircleH2 * q0q2CircleCircleDY) /
        q0q2CircleCircleD) *
        ((q0q2CircleCircleA * q0q2CircleCircleDX -
            Real.sqrt q0q2CircleCircleH2 * q0q2CircleCircleDY) /
          q0q2CircleCircleD) +
      ((q0q2CircleCircleA * q0q2CircleCircleDY +
          Real.sqrt q0q2CircleCircleH2 * q0q2CircleCircleDX) /
        q0q2CircleCircleD) *
        ((q0q2CircleCircleA * q0q2CircleCircleDY +
            Real.sqrt q0q2CircleCircleH2 * q0q2CircleCircleDX) /
          q0q2CircleCircleD) =
      (200 : ℝ) ^ 2 := by
  exact circleCircleUpper_q0_algebra
    q0q2CircleCircleDX q0q2CircleCircleDY q0q2CircleCircleD
    q0q2CircleCircleA (Real.sqrt q0q2CircleCircleH2)
    rfl q0q2CircleCircle_A_sq_add_H_sq_q0 q0q2CircleCircleD_ne

private theorem q0q2CircleCircleLower_q0_coordinate :
    ((q0q2CircleCircleA * q0q2CircleCircleDX +
          Real.sqrt q0q2CircleCircleH2 * q0q2CircleCircleDY) /
        q0q2CircleCircleD) *
        ((q0q2CircleCircleA * q0q2CircleCircleDX +
            Real.sqrt q0q2CircleCircleH2 * q0q2CircleCircleDY) /
          q0q2CircleCircleD) +
      ((q0q2CircleCircleA * q0q2CircleCircleDY -
          Real.sqrt q0q2CircleCircleH2 * q0q2CircleCircleDX) /
        q0q2CircleCircleD) *
        ((q0q2CircleCircleA * q0q2CircleCircleDY -
            Real.sqrt q0q2CircleCircleH2 * q0q2CircleCircleDX) /
          q0q2CircleCircleD) =
      (200 : ℝ) ^ 2 := by
  exact circleCircleLower_q0_algebra
    q0q2CircleCircleDX q0q2CircleCircleDY q0q2CircleCircleD
    q0q2CircleCircleA (Real.sqrt q0q2CircleCircleH2)
    rfl q0q2CircleCircle_A_sq_add_H_sq_q0 q0q2CircleCircleD_ne

private theorem q0q2CircleCircleUpper_q2_coordinate :
    (-(200 : ℝ) +
          (q0q2CircleCircleA * q0q2CircleCircleDX -
              Real.sqrt q0q2CircleCircleH2 * q0q2CircleCircleDY) /
            q0q2CircleCircleD -
        q0q2CenterX) *
        (-(200 : ℝ) +
            (q0q2CircleCircleA * q0q2CircleCircleDX -
                Real.sqrt q0q2CircleCircleH2 * q0q2CircleCircleDY) /
              q0q2CircleCircleD -
          q0q2CenterX) +
      ((q0q2CircleCircleA * q0q2CircleCircleDY +
            Real.sqrt q0q2CircleCircleH2 * q0q2CircleCircleDX) /
          q0q2CircleCircleD -
        q0q2CenterY) *
        ((q0q2CircleCircleA * q0q2CircleCircleDY +
              Real.sqrt q0q2CircleCircleH2 * q0q2CircleCircleDX) /
            q0q2CircleCircleD -
          q0q2CenterY) =
      (100 : ℝ) ^ 2 := by
  exact circleCircleUpper_q2_algebra
    q0q2CircleCircleDX q0q2CircleCircleDY q0q2CircleCircleD
    q0q2CircleCircleA (Real.sqrt q0q2CircleCircleH2)
    q0q2CenterX q0q2CenterY rfl rfl rfl
    q0q2CircleCircle_A_sub_D_sq_add_H_sq_q2 q0q2CircleCircleD_ne

private theorem q0q2CircleCircleLower_q2_coordinate :
    (-(200 : ℝ) +
          (q0q2CircleCircleA * q0q2CircleCircleDX +
              Real.sqrt q0q2CircleCircleH2 * q0q2CircleCircleDY) /
            q0q2CircleCircleD -
        q0q2CenterX) *
        (-(200 : ℝ) +
            (q0q2CircleCircleA * q0q2CircleCircleDX +
                Real.sqrt q0q2CircleCircleH2 * q0q2CircleCircleDY) /
              q0q2CircleCircleD -
          q0q2CenterX) +
      ((q0q2CircleCircleA * q0q2CircleCircleDY -
            Real.sqrt q0q2CircleCircleH2 * q0q2CircleCircleDX) /
          q0q2CircleCircleD -
        q0q2CenterY) *
        ((q0q2CircleCircleA * q0q2CircleCircleDY -
              Real.sqrt q0q2CircleCircleH2 * q0q2CircleCircleDX) /
            q0q2CircleCircleD -
          q0q2CenterY) =
      (100 : ℝ) ^ 2 := by
  exact circleCircleLower_q2_algebra
    q0q2CircleCircleDX q0q2CircleCircleDY q0q2CircleCircleD
    q0q2CircleCircleA (Real.sqrt q0q2CircleCircleH2)
    q0q2CenterX q0q2CenterY rfl rfl rfl
    q0q2CircleCircle_A_sub_D_sq_add_H_sq_q2 q0q2CircleCircleD_ne

theorem q0q2CircleCircleUpperPoint_mem_q0_circle :
    q0q2CircleCircleUpperPoint ∈
      circleSet karlssonOEISQ0.center karlssonOEISQ0.radius := by
  unfold q0q2CircleCircleUpperPoint circleSet
    TheoremOneEndToEnd.PaulsenLinearAlgebra.distSq2
    TheoremOneEndToEnd.PaulsenLinearAlgebra.normSq2
    TheoremOneEndToEnd.PaulsenLinearAlgebra.dot2
  simp [karlssonOEISQ0, EuclideanLollipop.fromAnchor, angleDirection,
    point2]
  exact q0q2CircleCircleUpper_q0_coordinate

theorem q0q2CircleCircleLowerPoint_mem_q0_circle :
    q0q2CircleCircleLowerPoint ∈
      circleSet karlssonOEISQ0.center karlssonOEISQ0.radius := by
  unfold q0q2CircleCircleLowerPoint circleSet
    TheoremOneEndToEnd.PaulsenLinearAlgebra.distSq2
    TheoremOneEndToEnd.PaulsenLinearAlgebra.normSq2
    TheoremOneEndToEnd.PaulsenLinearAlgebra.dot2
  simp [karlssonOEISQ0, EuclideanLollipop.fromAnchor, angleDirection,
    point2]
  exact q0q2CircleCircleLower_q0_coordinate

theorem q0q2CircleCircleUpperPoint_mem_q2_circle :
    q0q2CircleCircleUpperPoint ∈
      circleSet karlssonOEISQ2.center karlssonOEISQ2.radius := by
  unfold q0q2CircleCircleUpperPoint circleSet
    TheoremOneEndToEnd.PaulsenLinearAlgebra.distSq2
    TheoremOneEndToEnd.PaulsenLinearAlgebra.normSq2
    TheoremOneEndToEnd.PaulsenLinearAlgebra.dot2
  rw [q0q2_q2_center_eq]
  simp [karlssonOEISQ2, EuclideanLollipop.fromAnchor, point2]
  exact q0q2CircleCircleUpper_q2_coordinate

theorem q0q2CircleCircleLowerPoint_mem_q2_circle :
    q0q2CircleCircleLowerPoint ∈
      circleSet karlssonOEISQ2.center karlssonOEISQ2.radius := by
  unfold q0q2CircleCircleLowerPoint circleSet
    TheoremOneEndToEnd.PaulsenLinearAlgebra.distSq2
    TheoremOneEndToEnd.PaulsenLinearAlgebra.normSq2
    TheoremOneEndToEnd.PaulsenLinearAlgebra.dot2
  rw [q0q2_q2_center_eq]
  simp [karlssonOEISQ2, EuclideanLollipop.fromAnchor, point2]
  exact q0q2CircleCircleLower_q2_coordinate

theorem q0q2CircleCircleUpperPoint_mem_euclideanCircleCircleSet :
    toEuclideanR2 q0q2CircleCircleUpperPoint ∈
      euclideanCircleCircleSet karlssonOEISQ0 karlssonOEISQ2 := by
  constructor
  · exact
      (mem_circleSet_iff_mem_euclideanSphere
        karlssonOEISQ0.radius_pos.le).1
        q0q2CircleCircleUpperPoint_mem_q0_circle
  · exact
      (mem_circleSet_iff_mem_euclideanSphere
        karlssonOEISQ2.radius_pos.le).1
        q0q2CircleCircleUpperPoint_mem_q2_circle

theorem q0q2CircleCircleLowerPoint_mem_euclideanCircleCircleSet :
    toEuclideanR2 q0q2CircleCircleLowerPoint ∈
      euclideanCircleCircleSet karlssonOEISQ0 karlssonOEISQ2 := by
  constructor
  · exact
      (mem_circleSet_iff_mem_euclideanSphere
        karlssonOEISQ0.radius_pos.le).1
        q0q2CircleCircleLowerPoint_mem_q0_circle
  · exact
      (mem_circleSet_iff_mem_euclideanSphere
        karlssonOEISQ2.radius_pos.le).1
        q0q2CircleCircleLowerPoint_mem_q2_circle

theorem q0q2CircleCircleUpperPoint_mem_base_pairIntersectionSet :
    q0q2CircleCircleUpperPoint ∈
      karlssonOEISBaseArrangement.pairIntersectionSet
        (0 : Fin 4) (2 : Fin 4) := by
  exact
    OEISSevenPoint.pair_mem_of_euclideanCircleCircle
      (i := (0 : Fin 4)) (j := (2 : Fin 4))
      (p := q0q2CircleCircleUpperPoint)
      (by
        simpa [karlssonOEISBaseArrangement] using
          q0q2CircleCircleUpperPoint_mem_euclideanCircleCircleSet)

theorem q0q2CircleCircleLowerPoint_mem_base_pairIntersectionSet :
    q0q2CircleCircleLowerPoint ∈
      karlssonOEISBaseArrangement.pairIntersectionSet
        (0 : Fin 4) (2 : Fin 4) := by
  exact
    OEISSevenPoint.pair_mem_of_euclideanCircleCircle
      (i := (0 : Fin 4)) (j := (2 : Fin 4))
      (p := q0q2CircleCircleLowerPoint)
      (by
        simpa [karlssonOEISBaseArrangement] using
          q0q2CircleCircleLowerPoint_mem_euclideanCircleCircleSet)

private theorem q0q2Center_dist_sq_gt_hundred_sq :
    (100 : ℝ) ^ 2 < q0q2CenterX ^ 2 + q0q2CenterY ^ 2 := by
  unfold q0q2CenterX q0q2CenterY
  nlinarith [Real.sin_sq_add_cos_sq alpha, sin_alpha_pos, cos_alpha_pos]

private theorem q0q2RayCircleDiscriminant_lt_centerX_sq :
    q0q2RayCircleDiscriminant < q0q2CenterX ^ 2 := by
  unfold q0q2RayCircleDiscriminant
  nlinarith [q0q2Center_dist_sq_gt_hundred_sq]

private theorem q0q2RayCircle_sqrt_lt_centerX :
    Real.sqrt q0q2RayCircleDiscriminant < q0q2CenterX := by
  rw [Real.sqrt_lt q0q2RayCircleDiscriminant_nonneg
    q0q2CenterX_pos.le]
  exact q0q2RayCircleDiscriminant_lt_centerX_sq

private theorem q0q2RayCircle_sqrt_pos :
    0 < Real.sqrt q0q2RayCircleDiscriminant :=
  Real.sqrt_pos.2 q0q2RayCircleDiscriminant_pos

theorem q0q2RayCircleLeftPoint_x_pos :
    0 < q0q2RayCircleLeftPoint 0 := by
  unfold q0q2RayCircleLeftPoint
  simp [point2]
  nlinarith [q0q2RayCircle_sqrt_lt_centerX]

theorem q0q2RayCircleRightPoint_x_pos :
    0 < q0q2RayCircleRightPoint 0 := by
  unfold q0q2RayCircleRightPoint
  simp [point2]
  nlinarith [q0q2CenterX_pos, q0q2RayCircle_sqrt_pos]

theorem q0q2RayCircleLeftPoint_y_eq_zero :
    q0q2RayCircleLeftPoint 1 = 0 := by
  simp [q0q2RayCircleLeftPoint, point2]

theorem q0q2RayCircleRightPoint_y_eq_zero :
    q0q2RayCircleRightPoint 1 = 0 := by
  simp [q0q2RayCircleRightPoint, point2]

private theorem q0_xaxis_pos_not_mem_q0_circle
    {p : R2} (hx : 0 < p 0) (hy : p 1 = 0) :
    p ∉ circleSet karlssonOEISQ0.center karlssonOEISQ0.radius := by
  intro hp
  unfold circleSet
    TheoremOneEndToEnd.PaulsenLinearAlgebra.distSq2
    TheoremOneEndToEnd.PaulsenLinearAlgebra.normSq2
    TheoremOneEndToEnd.PaulsenLinearAlgebra.dot2 at hp
  simp [karlssonOEISQ0, EuclideanLollipop.fromAnchor, angleDirection,
    point2, hy] at hp
  nlinarith [hx]

theorem q0q2RayCircleLeftPoint_not_mem_q0_circle :
    q0q2RayCircleLeftPoint ∉
      circleSet karlssonOEISQ0.center karlssonOEISQ0.radius :=
  q0_xaxis_pos_not_mem_q0_circle
    q0q2RayCircleLeftPoint_x_pos q0q2RayCircleLeftPoint_y_eq_zero

theorem q0q2RayCircleRightPoint_not_mem_q0_circle :
    q0q2RayCircleRightPoint ∉
      circleSet karlssonOEISQ0.center karlssonOEISQ0.radius :=
  q0_xaxis_pos_not_mem_q0_circle
    q0q2RayCircleRightPoint_x_pos q0q2RayCircleRightPoint_y_eq_zero

theorem q0q2RayRayPoint_not_mem_q0_circle :
    q0q2RayRayPoint ∉
      circleSet karlssonOEISQ0.center karlssonOEISQ0.radius :=
  q0_xaxis_pos_not_mem_q0_circle
    q0q2RayRayPoint_x_pos q0q2RayRayPoint_y_eq_zero

private theorem q2_ray_point_not_mem_q2_circle_of_time_pos
    {t : ℝ} (ht : 0 < t) :
    karlssonOEISQ2.anchor + t • karlssonOEISQ2.rayDirection ∉
      circleSet karlssonOEISQ2.center karlssonOEISQ2.radius := by
  intro hp
  unfold circleSet
    TheoremOneEndToEnd.PaulsenLinearAlgebra.distSq2
    TheoremOneEndToEnd.PaulsenLinearAlgebra.normSq2
    TheoremOneEndToEnd.PaulsenLinearAlgebra.dot2 at hp
  simp [karlssonOEISQ2, EuclideanLollipop.fromAnchor, angleDirection,
    point2, q2_theta_cos, q2_theta_sin] at hp
  ring_nf at hp
  have htrig :
      Real.sin (Real.pi * (2 / 15 : ℝ)) ^ 2 +
          Real.cos (Real.pi * (2 / 15 : ℝ)) ^ 2 = 1 := by
    exact Real.sin_sq_add_cos_sq (Real.pi * (2 / 15 : ℝ))
  nlinarith [htrig, ht, hp]

private theorem q0q2CircleRay_sqrt_lt_dot :
    Real.sqrt q0q2CircleRayDiscriminant < q0q2CircleRayDot := by
  rw [Real.sqrt_lt q0q2CircleRayDiscriminant_nonneg
    q0q2CircleRayDot_pos.le]
  unfold q0q2CircleRayDiscriminant
  nlinarith [q0q2CircleRayConstant_pos]

theorem q0q2CircleRayNearTime_pos :
    0 < q0q2CircleRayNearTime := by
  unfold q0q2CircleRayNearTime
  nlinarith [q0q2CircleRay_sqrt_lt_dot]

theorem q0q2CircleRayFarTime_pos :
    0 < q0q2CircleRayFarTime := by
  unfold q0q2CircleRayFarTime
  nlinarith [q0q2CircleRayDot_pos,
    Real.sqrt_nonneg q0q2CircleRayDiscriminant]

theorem q0q2CircleRayNearPoint_not_mem_q2_circle :
    q0q2CircleRayNearPoint ∉
      circleSet karlssonOEISQ2.center karlssonOEISQ2.radius := by
  unfold q0q2CircleRayNearPoint
  exact
    q2_ray_point_not_mem_q2_circle_of_time_pos
      q0q2CircleRayNearTime_pos

theorem q0q2CircleRayFarPoint_not_mem_q2_circle :
    q0q2CircleRayFarPoint ∉
      circleSet karlssonOEISQ2.center karlssonOEISQ2.radius := by
  unfold q0q2CircleRayFarPoint
  exact
    q2_ray_point_not_mem_q2_circle_of_time_pos
      q0q2CircleRayFarTime_pos

theorem q0q2RayRayPoint_not_mem_q2_circle :
    q0q2RayRayPoint ∉
      circleSet karlssonOEISQ2.center karlssonOEISQ2.radius := by
  unfold q0q2RayRayPoint
  exact
    q2_ray_point_not_mem_q2_circle_of_time_pos
      q0q2RayRayTime_pos

theorem q0q2CircleCircleUpperPoint_ne_lower :
    q0q2CircleCircleUpperPoint ≠ q0q2CircleCircleLowerPoint := by
  intro h
  have hy := congr_fun h 1
  unfold q0q2CircleCircleUpperPoint q0q2CircleCircleLowerPoint at hy
  simp [point2] at hy
  change
    (q0q2CircleCircleA * q0q2CircleCircleDY +
          Real.sqrt q0q2CircleCircleH2 * q0q2CircleCircleDX) /
        q0q2CircleCircleD =
      (q0q2CircleCircleA * q0q2CircleCircleDY -
          Real.sqrt q0q2CircleCircleH2 * q0q2CircleCircleDX) /
        q0q2CircleCircleD at hy
  have hH : 0 < Real.sqrt q0q2CircleCircleH2 :=
    Real.sqrt_pos.2 q0q2CircleCircleH2_pos
  have hDX : 0 < q0q2CircleCircleDX := by
    nlinarith [q0q2CircleCircleDX_gt_hundred]
  have hdiff :
      ((q0q2CircleCircleA * q0q2CircleCircleDY +
            Real.sqrt q0q2CircleCircleH2 * q0q2CircleCircleDX) /
          q0q2CircleCircleD) -
        ((q0q2CircleCircleA * q0q2CircleCircleDY -
            Real.sqrt q0q2CircleCircleH2 * q0q2CircleCircleDX) /
          q0q2CircleCircleD) = 0 := by
    exact sub_eq_zero.2 hy
  have hdiff_eval :
      ((q0q2CircleCircleA * q0q2CircleCircleDY +
            Real.sqrt q0q2CircleCircleH2 * q0q2CircleCircleDX) /
          q0q2CircleCircleD) -
        ((q0q2CircleCircleA * q0q2CircleCircleDY -
            Real.sqrt q0q2CircleCircleH2 * q0q2CircleCircleDX) /
          q0q2CircleCircleD) =
        (2 * Real.sqrt q0q2CircleCircleH2 *
            q0q2CircleCircleDX) / q0q2CircleCircleD := by
    field_simp [q0q2CircleCircleD_ne]
    ring
  have hpos :
      0 <
        (2 * Real.sqrt q0q2CircleCircleH2 *
            q0q2CircleCircleDX) / q0q2CircleCircleD := by
    exact div_pos (mul_pos (mul_pos (by norm_num) hH) hDX)
      q0q2CircleCircleD_pos
  rw [hdiff_eval] at hdiff
  nlinarith

theorem q0q2CircleRayNearPoint_ne_far :
    q0q2CircleRayNearPoint ≠ q0q2CircleRayFarPoint := by
  intro h
  have hy := congr_fun h 1
  unfold q0q2CircleRayNearPoint q0q2CircleRayFarPoint
    q0q2CircleRayNearTime q0q2CircleRayFarTime at hy
  simp [karlssonOEISQ2, EuclideanLollipop.fromAnchor, angleDirection,
    point2, q2_theta_sin] at hy
  have hsqrt : 0 < Real.sqrt q0q2CircleRayDiscriminant :=
    Real.sqrt_pos.2 q0q2CircleRayDiscriminant_pos
  rcases hy with htime | hcos
  · nlinarith [hsqrt, htime]
  · exact cos_alpha_pos.ne' hcos

theorem q0q2RayCircleLeftPoint_ne_right :
    q0q2RayCircleLeftPoint ≠ q0q2RayCircleRightPoint := by
  intro h
  have hx := congr_fun h 0
  unfold q0q2RayCircleLeftPoint q0q2RayCircleRightPoint at hx
  simp [point2] at hx
  nlinarith [q0q2RayCircle_sqrt_pos]

private theorem ne_of_left_mem_q0_circle_of_right_not_mem_q0_circle
    {p q : R2}
    (hp : p ∈ circleSet karlssonOEISQ0.center karlssonOEISQ0.radius)
    (hq : q ∉ circleSet karlssonOEISQ0.center karlssonOEISQ0.radius) :
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

theorem q0q2CircleCircleUpperPoint_ne_circleRayNear :
    q0q2CircleCircleUpperPoint ≠ q0q2CircleRayNearPoint :=
  ne_of_left_mem_q2_circle_of_right_not_mem_q2_circle
    q0q2CircleCircleUpperPoint_mem_q2_circle
    q0q2CircleRayNearPoint_not_mem_q2_circle

theorem q0q2CircleCircleUpperPoint_ne_circleRayFar :
    q0q2CircleCircleUpperPoint ≠ q0q2CircleRayFarPoint :=
  ne_of_left_mem_q2_circle_of_right_not_mem_q2_circle
    q0q2CircleCircleUpperPoint_mem_q2_circle
    q0q2CircleRayFarPoint_not_mem_q2_circle

theorem q0q2CircleCircleLowerPoint_ne_circleRayNear :
    q0q2CircleCircleLowerPoint ≠ q0q2CircleRayNearPoint :=
  ne_of_left_mem_q2_circle_of_right_not_mem_q2_circle
    q0q2CircleCircleLowerPoint_mem_q2_circle
    q0q2CircleRayNearPoint_not_mem_q2_circle

theorem q0q2CircleCircleLowerPoint_ne_circleRayFar :
    q0q2CircleCircleLowerPoint ≠ q0q2CircleRayFarPoint :=
  ne_of_left_mem_q2_circle_of_right_not_mem_q2_circle
    q0q2CircleCircleLowerPoint_mem_q2_circle
    q0q2CircleRayFarPoint_not_mem_q2_circle

theorem q0q2CircleCircleUpperPoint_ne_rayCircleLeft :
    q0q2CircleCircleUpperPoint ≠ q0q2RayCircleLeftPoint :=
  ne_of_left_mem_q0_circle_of_right_not_mem_q0_circle
    q0q2CircleCircleUpperPoint_mem_q0_circle
    q0q2RayCircleLeftPoint_not_mem_q0_circle

theorem q0q2CircleCircleUpperPoint_ne_rayCircleRight :
    q0q2CircleCircleUpperPoint ≠ q0q2RayCircleRightPoint :=
  ne_of_left_mem_q0_circle_of_right_not_mem_q0_circle
    q0q2CircleCircleUpperPoint_mem_q0_circle
    q0q2RayCircleRightPoint_not_mem_q0_circle

theorem q0q2CircleCircleUpperPoint_ne_rayRay :
    q0q2CircleCircleUpperPoint ≠ q0q2RayRayPoint :=
  ne_of_left_mem_q0_circle_of_right_not_mem_q0_circle
    q0q2CircleCircleUpperPoint_mem_q0_circle
    q0q2RayRayPoint_not_mem_q0_circle

theorem q0q2CircleCircleLowerPoint_ne_rayCircleLeft :
    q0q2CircleCircleLowerPoint ≠ q0q2RayCircleLeftPoint :=
  ne_of_left_mem_q0_circle_of_right_not_mem_q0_circle
    q0q2CircleCircleLowerPoint_mem_q0_circle
    q0q2RayCircleLeftPoint_not_mem_q0_circle

theorem q0q2CircleCircleLowerPoint_ne_rayCircleRight :
    q0q2CircleCircleLowerPoint ≠ q0q2RayCircleRightPoint :=
  ne_of_left_mem_q0_circle_of_right_not_mem_q0_circle
    q0q2CircleCircleLowerPoint_mem_q0_circle
    q0q2RayCircleRightPoint_not_mem_q0_circle

theorem q0q2CircleCircleLowerPoint_ne_rayRay :
    q0q2CircleCircleLowerPoint ≠ q0q2RayRayPoint :=
  ne_of_left_mem_q0_circle_of_right_not_mem_q0_circle
    q0q2CircleCircleLowerPoint_mem_q0_circle
    q0q2RayRayPoint_not_mem_q0_circle

theorem q0q2CircleRayNearPoint_ne_rayCircleLeft :
    q0q2CircleRayNearPoint ≠ q0q2RayCircleLeftPoint :=
  ne_of_left_mem_q0_circle_of_right_not_mem_q0_circle
    q0q2CircleRayNearPoint_mem_q0_circle
    q0q2RayCircleLeftPoint_not_mem_q0_circle

theorem q0q2CircleRayNearPoint_ne_rayCircleRight :
    q0q2CircleRayNearPoint ≠ q0q2RayCircleRightPoint :=
  ne_of_left_mem_q0_circle_of_right_not_mem_q0_circle
    q0q2CircleRayNearPoint_mem_q0_circle
    q0q2RayCircleRightPoint_not_mem_q0_circle

theorem q0q2CircleRayNearPoint_ne_rayRay :
    q0q2CircleRayNearPoint ≠ q0q2RayRayPoint :=
  ne_of_left_mem_q0_circle_of_right_not_mem_q0_circle
    q0q2CircleRayNearPoint_mem_q0_circle
    q0q2RayRayPoint_not_mem_q0_circle

theorem q0q2CircleRayFarPoint_ne_rayCircleLeft :
    q0q2CircleRayFarPoint ≠ q0q2RayCircleLeftPoint :=
  ne_of_left_mem_q0_circle_of_right_not_mem_q0_circle
    q0q2CircleRayFarPoint_mem_q0_circle
    q0q2RayCircleLeftPoint_not_mem_q0_circle

theorem q0q2CircleRayFarPoint_ne_rayCircleRight :
    q0q2CircleRayFarPoint ≠ q0q2RayCircleRightPoint :=
  ne_of_left_mem_q0_circle_of_right_not_mem_q0_circle
    q0q2CircleRayFarPoint_mem_q0_circle
    q0q2RayCircleRightPoint_not_mem_q0_circle

theorem q0q2CircleRayFarPoint_ne_rayRay :
    q0q2CircleRayFarPoint ≠ q0q2RayRayPoint :=
  ne_of_left_mem_q0_circle_of_right_not_mem_q0_circle
    q0q2CircleRayFarPoint_mem_q0_circle
    q0q2RayRayPoint_not_mem_q0_circle

theorem q0q2RayCircleLeftPoint_ne_rayRay :
    q0q2RayCircleLeftPoint ≠ q0q2RayRayPoint :=
  ne_of_left_mem_q2_circle_of_right_not_mem_q2_circle
    q0q2RayCircleLeftPoint_mem_q2_circle
    q0q2RayRayPoint_not_mem_q2_circle

theorem q0q2RayCircleRightPoint_ne_rayRay :
    q0q2RayCircleRightPoint ≠ q0q2RayRayPoint :=
  ne_of_left_mem_q2_circle_of_right_not_mem_q2_circle
    q0q2RayCircleRightPoint_mem_q2_circle
    q0q2RayRayPoint_not_mem_q2_circle

/-- The seven explicit labelled component points for `(Q0,Q2)`. -/
noncomputable def q0q2SevenPointFinset : Finset R2 :=
  {q0q2CircleCircleUpperPoint, q0q2CircleCircleLowerPoint,
    q0q2CircleRayNearPoint, q0q2CircleRayFarPoint,
    q0q2RayCircleLeftPoint, q0q2RayCircleRightPoint,
    q0q2RayRayPoint}

theorem q0q2SevenPointFinset_card :
    q0q2SevenPointFinset.card = 7 := by
  classical
  simp [q0q2SevenPointFinset,
    q0q2CircleCircleUpperPoint_ne_lower,
    q0q2CircleCircleUpperPoint_ne_circleRayNear,
    q0q2CircleCircleUpperPoint_ne_circleRayFar,
    q0q2CircleCircleUpperPoint_ne_rayCircleLeft,
    q0q2CircleCircleUpperPoint_ne_rayCircleRight,
    q0q2CircleCircleUpperPoint_ne_rayRay,
    q0q2CircleCircleLowerPoint_ne_circleRayNear,
    q0q2CircleCircleLowerPoint_ne_circleRayFar,
    q0q2CircleCircleLowerPoint_ne_rayCircleLeft,
    q0q2CircleCircleLowerPoint_ne_rayCircleRight,
    q0q2CircleCircleLowerPoint_ne_rayRay,
    q0q2CircleRayNearPoint_ne_far,
    q0q2CircleRayNearPoint_ne_rayCircleLeft,
    q0q2CircleRayNearPoint_ne_rayCircleRight,
    q0q2CircleRayNearPoint_ne_rayRay,
    q0q2CircleRayFarPoint_ne_rayCircleLeft,
    q0q2CircleRayFarPoint_ne_rayCircleRight,
    q0q2CircleRayFarPoint_ne_rayRay,
    q0q2RayCircleLeftPoint_ne_right,
    q0q2RayCircleLeftPoint_ne_rayRay,
    q0q2RayCircleRightPoint_ne_rayRay]

theorem q0q2SevenPointFinset_subset :
    ∀ p ∈ q0q2SevenPointFinset,
      p ∈ karlssonOEISBaseArrangement.pairIntersectionSet
        (0 : Fin 4) (2 : Fin 4) := by
  intro p hp
  simp [q0q2SevenPointFinset] at hp
  rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact q0q2CircleCircleUpperPoint_mem_base_pairIntersectionSet
  · exact q0q2CircleCircleLowerPoint_mem_base_pairIntersectionSet
  · exact q0q2CircleRayNearPoint_mem_base_pairIntersectionSet
  · exact q0q2CircleRayFarPoint_mem_base_pairIntersectionSet
  · exact q0q2RayCircleLeftPoint_mem_base_pairIntersectionSet
  · exact q0q2RayCircleRightPoint_mem_base_pairIntersectionSet
  · exact q0q2RayRayPoint_mem_base_pairIntersectionSet

/-- Seven-point lower witness for the exact OEIS base pair `(Q0,Q2)`. -/
noncomputable def q0q2SevenPointSubset :
    OEISSevenPoint.SevenPointSubset (0 : Fin 4) (2 : Fin 4) where
  points := q0q2SevenPointFinset
  card_eq_seven := q0q2SevenPointFinset_card
  points_subset := q0q2SevenPointFinset_subset

/-- Exact pair-coordinate crossing certificate for `(Q0,Q2)`. -/
noncomputable def q0q2PairCoordinateCrossingCertificate :
    KarlssonOEISBasePairCoordinateCrossingCertificate
      (0 : Fin 4) (2 : Fin 4) (by decide) :=
  OEISSevenPoint.pair02Certificate q0q2SevenPointSubset

end

end OEISPair02
end CompleteFormalization
end TheoremOneManuscript
end Lollipop
