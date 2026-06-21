import Lollipop.Internal.Manuscript.CompleteFormalization.OEISSevenPoint
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.Analysis.Real.Sqrt
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds

/-!
Concrete component witnesses for the OEIS/Karlsson base pair `(Q0,Q3)`.

This file completes the non-exceptional exact `= 7` work for `(Q0,Q3)` by
constructing the full seven-component witness used by the
`SevenComponentWitness` interface from `OEISSevenPoint.lean`.
-/

namespace Lollipop
namespace TheoremOneManuscript
namespace CompleteFormalization

open PrimitiveGeometry

namespace OEISPair03

noncomputable section

open ExplicitInputs
open TheoremOneEndToEnd.PaulsenLinearAlgebra (distSq2 normSq2 dot2)

private abbrev beta : ℝ := Real.pi / 30

private theorem beta_pos : 0 < beta := by
  dsimp [beta]
  nlinarith [Real.pi_pos]

private theorem beta_lt_pi_div_four : beta < Real.pi / 4 := by
  dsimp [beta]
  nlinarith [Real.pi_pos]

private theorem beta_lt_pi_div_two : beta < Real.pi / 2 := by
  exact beta_lt_pi_div_four.trans (by nlinarith [Real.pi_pos])

private theorem cos_beta_pos : 0 < Real.cos beta := by
  apply Real.cos_pos_of_mem_Ioo
  constructor
  · nlinarith [beta_pos, Real.pi_pos]
  · exact beta_lt_pi_div_two

private theorem sin_beta_pos : 0 < Real.sin beta := by
  apply Real.sin_pos_of_pos_of_lt_pi
  · exact beta_pos
  · nlinarith [beta_lt_pi_div_two, Real.pi_pos]

private theorem sin_beta_lt_cos_beta :
    Real.sin beta < Real.cos beta := by
  have h :
      Real.cos (Real.pi / 2 - beta) < Real.cos beta :=
    Real.cos_lt_cos_of_nonneg_of_le_pi_div_two
      beta_pos.le
      (by nlinarith [beta_pos])
      (by nlinarith [beta_lt_pi_div_four])
  simpa [Real.cos_pi_div_two_sub] using h

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

/-- Forward time along the `Q3` ray until it hits the `Q0` ray's x-axis. -/
noncomputable def q0q3RayRayTime : ℝ :=
  ((5 : ℝ) / 100) / Real.cos beta

/-- The concrete ray-ray point for the OEIS/Karlsson pair `(Q0,Q3)`. -/
noncomputable def q0q3RayRayPoint : R2 :=
  karlssonOEISQ3.anchor + q0q3RayRayTime • karlssonOEISQ3.rayDirection

theorem q0q3RayRayTime_pos : 0 < q0q3RayRayTime := by
  unfold q0q3RayRayTime
  exact div_pos (by norm_num) cos_beta_pos

theorem q0q3RayRayPoint_y_eq_zero :
    q0q3RayRayPoint 1 = 0 := by
  have hcos_ne : Real.cos beta ≠ 0 := cos_beta_pos.ne'
  unfold q0q3RayRayPoint q0q3RayRayTime
  simp [karlssonOEISQ3, EuclideanLollipop.fromAnchor,
    angleDirection, point2, q3_theta_sin, beta]
  field_simp [hcos_ne]
  ring

theorem q0q3RayRayPoint_x_pos :
    0 < q0q3RayRayPoint 0 := by
  have hcos_ne : Real.cos beta ≠ 0 := cos_beta_pos.ne'
  have htan_lt_one :
      Real.sin beta / Real.cos beta < 1 := by
    rw [div_lt_one cos_beta_pos]
    exact sin_beta_lt_cos_beta
  have htan_lt_one' :
      Real.sin (Real.pi / 30) / Real.cos (Real.pi / 30) < 1 := by
    simpa [beta] using htan_lt_one
  have hscaled :
      ((5 : ℝ) / 100) * Real.sin (Real.pi / 30) /
          Real.cos (Real.pi / 30) < (5 : ℝ) / 100 := by
    have hmul :=
      mul_lt_mul_of_pos_left htan_lt_one'
        (by norm_num : (0 : ℝ) < (5 : ℝ) / 100)
    simpa [mul_div_assoc] using hmul
  have hanchor : (5 : ℝ) / 100 < karlssonOEISQ3AnchorX := by
    norm_num [karlssonOEISQ3AnchorX]
  have hscaled100 :
      5 * Real.sin (Real.pi / 30) / Real.cos (Real.pi / 30) < 5 := by
    have hmul :=
      mul_lt_mul_of_pos_left htan_lt_one'
        (by norm_num : (0 : ℝ) < 5)
    simpa [mul_div_assoc] using hmul
  have hanchor100 : 5 < 100 * karlssonOEISQ3AnchorX := by
    nlinarith [hanchor]
  unfold q0q3RayRayPoint q0q3RayRayTime
  simp [karlssonOEISQ3, EuclideanLollipop.fromAnchor,
    angleDirection, point2, q3_theta_cos, beta]
  field_simp [hcos_ne]
  nlinarith [hscaled100, hanchor100]

theorem q0q3RayRayPoint_mem_q3_ray :
    q0q3RayRayPoint ∈
      raySet karlssonOEISQ3.anchor karlssonOEISQ3.rayDirection := by
  exact ⟨q0q3RayRayTime, q0q3RayRayTime_pos.le, rfl⟩

theorem q0q3RayRayPoint_mem_q0_ray :
    q0q3RayRayPoint ∈
      raySet karlssonOEISQ0.anchor karlssonOEISQ0.rayDirection := by
  refine ⟨q0q3RayRayPoint 0, q0q3RayRayPoint_x_pos.le, ?_⟩
  ext i
  fin_cases i
  · simp [karlssonOEISQ0, EuclideanLollipop.fromAnchor,
      angleDirection, point2]
  · simp [karlssonOEISQ0, EuclideanLollipop.fromAnchor,
      angleDirection, point2, q0q3RayRayPoint_y_eq_zero]

/-- Lifted ray-ray component form of the concrete `(Q0,Q3)` ray-ray point. -/
theorem q0q3RayRayPoint_mem_euclideanRayRaySet :
    toEuclideanR2 q0q3RayRayPoint ∈
      euclideanRayRaySet karlssonOEISQ0 karlssonOEISQ3 := by
  constructor
  · exact
      (mem_raySet_iff_mem_euclideanRaySet
        (p := q0q3RayRayPoint)
        (anchor := karlssonOEISQ0.anchor)
        (direction := karlssonOEISQ0.rayDirection)).1
        q0q3RayRayPoint_mem_q0_ray
  · exact
      (mem_raySet_iff_mem_euclideanRaySet
        (p := q0q3RayRayPoint)
        (anchor := karlssonOEISQ3.anchor)
        (direction := karlssonOEISQ3.rayDirection)).1
        q0q3RayRayPoint_mem_q3_ray

/-- Arrangement-indexed primitive carrier-intersection form. -/
theorem q0q3RayRayPoint_mem_base_pairIntersectionSet :
    q0q3RayRayPoint ∈
      karlssonOEISBaseArrangement.pairIntersectionSet
        (0 : Fin 4) (3 : Fin 4) := by
  exact
    OEISSevenPoint.pair_mem_of_euclideanRayRay
      (i := (0 : Fin 4)) (j := (3 : Fin 4))
      (p := q0q3RayRayPoint)
      (by
        simpa [karlssonOEISBaseArrangement] using
          q0q3RayRayPoint_mem_euclideanRayRaySet)

/-- The `x`-coordinate of the center of `Q3`, expressed in terms of
`beta = π/30`. -/
private abbrev q0q3CenterX : ℝ :=
  karlssonOEISQ3AnchorX + 100 * Real.sin beta

/-- The `y`-coordinate of the center of `Q3`, expressed in terms of
`beta = π/30`. -/
private abbrev q0q3CenterY : ℝ :=
  -((5 : ℝ) / 100) - 100 * Real.cos beta

/-- The x-axis discriminant for `ray(Q0) ∩ circle(Q3)`. -/
private abbrev q0q3RayCircleDiscriminant : ℝ :=
  (100 : ℝ) ^ 2 - q0q3CenterY ^ 2

private theorem q0q3_q3_center_eq :
    karlssonOEISQ3.center = point2 q0q3CenterX q0q3CenterY := by
  ext i
  fin_cases i <;>
    simp [karlssonOEISQ3, EuclideanLollipop.fromAnchor, angleDirection,
      point2, q0q3CenterX, q0q3CenterY, q3_theta_cos, q3_theta_sin]

private theorem q0q3CenterX_pos : 0 < q0q3CenterX := by
  have hanchor_pos : 0 < karlssonOEISQ3AnchorX := by
    norm_num [karlssonOEISQ3AnchorX]
  unfold q0q3CenterX
  nlinarith [sin_beta_pos, hanchor_pos]

private theorem q0q3CenterY_neg : q0q3CenterY < 0 := by
  unfold q0q3CenterY
  nlinarith [cos_beta_pos]

private theorem cos_beta_le_four_four_nine_div_four_fifty :
    Real.cos beta ≤ (449 : ℝ) / 450 := by
  have habs : |beta| ≤ Real.pi := by
    rw [abs_of_nonneg beta_pos.le]
    nlinarith [beta_lt_pi_div_two, Real.pi_pos]
  calc
    Real.cos beta ≤ 1 - 2 / Real.pi ^ 2 * beta ^ 2 :=
      Real.cos_le_one_sub_mul_cos_sq habs
    _ = (449 : ℝ) / 450 := by
      dsimp [beta]
      field_simp [Real.pi_pos.ne']
      ring

private theorem q0q3CenterY_lt_hundred : q0q3CenterY < 100 := by
  nlinarith [q0q3CenterY_neg]

private theorem neg_hundred_lt_q0q3CenterY : -(100 : ℝ) < q0q3CenterY := by
  unfold q0q3CenterY
  nlinarith [cos_beta_le_four_four_nine_div_four_fifty]

private theorem q0q3RayCircleDiscriminant_pos :
    0 < q0q3RayCircleDiscriminant := by
  unfold q0q3RayCircleDiscriminant
  have hprod :
      0 < (100 - q0q3CenterY) * (100 + q0q3CenterY) :=
    mul_pos (sub_pos.2 q0q3CenterY_lt_hundred)
      (by nlinarith [neg_hundred_lt_q0q3CenterY])
  nlinarith [hprod]

private theorem q0q3RayCircleDiscriminant_nonneg :
    0 ≤ q0q3RayCircleDiscriminant :=
  q0q3RayCircleDiscriminant_pos.le

private theorem q0q3RayCircleDiscriminant_le_centerX_sq :
    q0q3RayCircleDiscriminant ≤ q0q3CenterX ^ 2 := by
  unfold q0q3RayCircleDiscriminant
  have hcenter_dist :
      (100 : ℝ) ^ 2 < q0q3CenterX ^ 2 + q0q3CenterY ^ 2 := by
    have hanchor_pos : 0 < karlssonOEISQ3AnchorX := by
      norm_num [karlssonOEISQ3AnchorX]
    unfold q0q3CenterX q0q3CenterY
    nlinarith [Real.sin_sq_add_cos_sq beta, sin_beta_pos, cos_beta_pos,
      hanchor_pos]
  nlinarith [hcenter_dist]

private theorem q0q3RayCircle_sqrt_le_centerX :
    Real.sqrt q0q3RayCircleDiscriminant ≤ q0q3CenterX := by
  rw [Real.sqrt_le_iff]
  exact ⟨q0q3CenterX_pos.le, q0q3RayCircleDiscriminant_le_centerX_sq⟩

/-- Left x-axis intersection of the `Q0` ray with the `Q3` circle. -/
noncomputable def q0q3RayCircleLeftPoint : R2 :=
  point2 (q0q3CenterX - Real.sqrt q0q3RayCircleDiscriminant) 0

/-- Right x-axis intersection of the `Q0` ray with the `Q3` circle. -/
noncomputable def q0q3RayCircleRightPoint : R2 :=
  point2 (q0q3CenterX + Real.sqrt q0q3RayCircleDiscriminant) 0

theorem q0q3RayCircleLeftPoint_x_nonneg :
    0 ≤ q0q3RayCircleLeftPoint 0 := by
  unfold q0q3RayCircleLeftPoint
  simp [point2]
  nlinarith [q0q3RayCircle_sqrt_le_centerX]

theorem q0q3RayCircleRightPoint_x_nonneg :
    0 ≤ q0q3RayCircleRightPoint 0 := by
  unfold q0q3RayCircleRightPoint
  simp [point2]
  nlinarith [q0q3CenterX_pos, Real.sqrt_nonneg q0q3RayCircleDiscriminant]

theorem q0q3RayCircleLeftPoint_mem_q0_ray :
    q0q3RayCircleLeftPoint ∈
      raySet karlssonOEISQ0.anchor karlssonOEISQ0.rayDirection := by
  refine ⟨q0q3RayCircleLeftPoint 0,
    q0q3RayCircleLeftPoint_x_nonneg, ?_⟩
  ext i
  fin_cases i <;>
    simp [q0q3RayCircleLeftPoint, karlssonOEISQ0,
      EuclideanLollipop.fromAnchor, angleDirection, point2]

theorem q0q3RayCircleRightPoint_mem_q0_ray :
    q0q3RayCircleRightPoint ∈
      raySet karlssonOEISQ0.anchor karlssonOEISQ0.rayDirection := by
  refine ⟨q0q3RayCircleRightPoint 0,
    q0q3RayCircleRightPoint_x_nonneg, ?_⟩
  ext i
  fin_cases i <;>
    simp [q0q3RayCircleRightPoint, karlssonOEISQ0,
      EuclideanLollipop.fromAnchor, angleDirection, point2]

theorem q0q3RayCircleLeftPoint_mem_q3_circle :
    q0q3RayCircleLeftPoint ∈
      circleSet karlssonOEISQ3.center karlssonOEISQ3.radius := by
  unfold q0q3RayCircleLeftPoint circleSet
    TheoremOneEndToEnd.PaulsenLinearAlgebra.distSq2
    TheoremOneEndToEnd.PaulsenLinearAlgebra.normSq2
    TheoremOneEndToEnd.PaulsenLinearAlgebra.dot2
  rw [q0q3_q3_center_eq]
  simp [point2, q0q3RayCircleDiscriminant]
  rw [Real.mul_self_sqrt
    (by
      simpa [q0q3RayCircleDiscriminant] using
        q0q3RayCircleDiscriminant_nonneg)]
  simp [karlssonOEISQ3, EuclideanLollipop.fromAnchor, q0q3CenterY]
  ring

theorem q0q3RayCircleRightPoint_mem_q3_circle :
    q0q3RayCircleRightPoint ∈
      circleSet karlssonOEISQ3.center karlssonOEISQ3.radius := by
  unfold q0q3RayCircleRightPoint circleSet
    TheoremOneEndToEnd.PaulsenLinearAlgebra.distSq2
    TheoremOneEndToEnd.PaulsenLinearAlgebra.normSq2
    TheoremOneEndToEnd.PaulsenLinearAlgebra.dot2
  rw [q0q3_q3_center_eq]
  simp [point2, q0q3RayCircleDiscriminant]
  rw [Real.mul_self_sqrt
    (by
      simpa [q0q3RayCircleDiscriminant] using
        q0q3RayCircleDiscriminant_nonneg)]
  simp [karlssonOEISQ3, EuclideanLollipop.fromAnchor, q0q3CenterY]
  ring

theorem q0q3RayCircleLeftPoint_mem_euclideanRayCircleSet :
    toEuclideanR2 q0q3RayCircleLeftPoint ∈
      euclideanRayCircleSet karlssonOEISQ0 karlssonOEISQ3 := by
  constructor
  · exact
      (mem_raySet_iff_mem_euclideanRaySet
        (p := q0q3RayCircleLeftPoint)
        (anchor := karlssonOEISQ0.anchor)
        (direction := karlssonOEISQ0.rayDirection)).1
        q0q3RayCircleLeftPoint_mem_q0_ray
  · exact
      (mem_circleSet_iff_mem_euclideanSphere
        karlssonOEISQ3.radius_pos.le).1
        q0q3RayCircleLeftPoint_mem_q3_circle

theorem q0q3RayCircleRightPoint_mem_euclideanRayCircleSet :
    toEuclideanR2 q0q3RayCircleRightPoint ∈
      euclideanRayCircleSet karlssonOEISQ0 karlssonOEISQ3 := by
  constructor
  · exact
      (mem_raySet_iff_mem_euclideanRaySet
        (p := q0q3RayCircleRightPoint)
        (anchor := karlssonOEISQ0.anchor)
        (direction := karlssonOEISQ0.rayDirection)).1
        q0q3RayCircleRightPoint_mem_q0_ray
  · exact
      (mem_circleSet_iff_mem_euclideanSphere
        karlssonOEISQ3.radius_pos.le).1
        q0q3RayCircleRightPoint_mem_q3_circle

theorem q0q3RayCircleLeftPoint_mem_base_pairIntersectionSet :
    q0q3RayCircleLeftPoint ∈
      karlssonOEISBaseArrangement.pairIntersectionSet
        (0 : Fin 4) (3 : Fin 4) := by
  exact
    OEISSevenPoint.pair_mem_of_euclideanRayCircle
      (i := (0 : Fin 4)) (j := (3 : Fin 4))
      (p := q0q3RayCircleLeftPoint)
      (by
        simpa [karlssonOEISBaseArrangement] using
          q0q3RayCircleLeftPoint_mem_euclideanRayCircleSet)

theorem q0q3RayCircleRightPoint_mem_base_pairIntersectionSet :
    q0q3RayCircleRightPoint ∈
      karlssonOEISBaseArrangement.pairIntersectionSet
        (0 : Fin 4) (3 : Fin 4) := by
  exact
    OEISSevenPoint.pair_mem_of_euclideanRayCircle
      (i := (0 : Fin 4)) (j := (3 : Fin 4))
      (p := q0q3RayCircleRightPoint)
      (by
        simpa [karlssonOEISBaseArrangement] using
          q0q3RayCircleRightPoint_mem_euclideanRayCircleSet)

/-- The positive dot coefficient in the quadratic for
`circle(Q0) ∩ ray(Q3)`. -/
private abbrev q0q3CircleRayDot : ℝ :=
  ((200 : ℝ) + karlssonOEISQ3AnchorX) * Real.sin beta +
    ((5 : ℝ) / 100) * Real.cos beta

/-- The constant term in the quadratic for `circle(Q0) ∩ ray(Q3)`. -/
private abbrev q0q3CircleRayConstant : ℝ :=
  ((200 : ℝ) + karlssonOEISQ3AnchorX) ^ 2 +
    ((5 : ℝ) / 100) ^ 2 - (200 : ℝ) ^ 2

/-- The discriminant for the two intersections of `circle(Q0)` with the
`Q3` ray. -/
private abbrev q0q3CircleRayDiscriminant : ℝ :=
  q0q3CircleRayDot ^ 2 - q0q3CircleRayConstant

private theorem beta_le_one : beta ≤ 1 := by
  dsimp [beta]
  nlinarith [Real.pi_lt_four]

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

private theorem nine_div_ten_lt_cos_beta :
    (9 : ℝ) / 10 < Real.cos beta := by
  have hcos := Real.one_sub_sq_div_two_lt_cos (x := beta) beta_pos.ne'
  have hbeta_lt : beta < (2 : ℝ) / 15 := by
    dsimp [beta]
    nlinarith [Real.pi_lt_four]
  nlinarith [hcos, beta_pos, hbeta_lt]

private theorem q0q3CircleRayDot_gt_base :
    ((200 : ℝ) + karlssonOEISQ3AnchorX) * ((13 : ℝ) / 125) <
      q0q3CircleRayDot := by
  have hcoef_pos : 0 < (200 : ℝ) + karlssonOEISQ3AnchorX := by
    norm_num [karlssonOEISQ3AnchorX]
  have hmul :=
    mul_lt_mul_of_pos_left thirteen_div_one_twenty_five_lt_sin_beta
      hcoef_pos
  unfold q0q3CircleRayDot
  nlinarith [hmul, cos_beta_pos]

private theorem q0q3CircleRay_base_pos :
    0 < ((200 : ℝ) + karlssonOEISQ3AnchorX) * ((13 : ℝ) / 125) := by
  have hcoef_pos : 0 < (200 : ℝ) + karlssonOEISQ3AnchorX := by
    norm_num [karlssonOEISQ3AnchorX]
  positivity

private theorem q0q3CircleRayDot_pos : 0 < q0q3CircleRayDot := by
  exact q0q3CircleRay_base_pos.trans q0q3CircleRayDot_gt_base

private theorem q0q3CircleRayConstant_pos :
    0 < q0q3CircleRayConstant := by
  norm_num [q0q3CircleRayConstant, karlssonOEISQ3AnchorX]

private theorem q0q3CircleRayDiscriminant_pos :
    0 < q0q3CircleRayDiscriminant := by
  unfold q0q3CircleRayDiscriminant
  have hbase :
      q0q3CircleRayConstant <
        (((200 : ℝ) + karlssonOEISQ3AnchorX) * ((13 : ℝ) / 125)) ^ 2 := by
    norm_num [q0q3CircleRayConstant, karlssonOEISQ3AnchorX]
  have hsq :
      (((200 : ℝ) + karlssonOEISQ3AnchorX) * ((13 : ℝ) / 125)) ^ 2 <
        q0q3CircleRayDot ^ 2 := by
    nlinarith [q0q3CircleRayDot_gt_base, q0q3CircleRay_base_pos]
  exact sub_pos.2 (hbase.trans hsq)

private theorem q0q3CircleRayDiscriminant_nonneg :
    0 ≤ q0q3CircleRayDiscriminant :=
  q0q3CircleRayDiscriminant_pos.le

private theorem q0q3CircleRay_sqrt_le_dot :
    Real.sqrt q0q3CircleRayDiscriminant ≤ q0q3CircleRayDot := by
  rw [Real.sqrt_le_iff]
  exact ⟨q0q3CircleRayDot_pos.le, by
    unfold q0q3CircleRayDiscriminant
    nlinarith [q0q3CircleRayConstant_pos]⟩

/-- Near forward time along the `Q3` ray at which it hits the `Q0` circle. -/
noncomputable def q0q3CircleRayNearTime : ℝ :=
  q0q3CircleRayDot - Real.sqrt q0q3CircleRayDiscriminant

/-- Far forward time along the `Q3` ray at which it hits the `Q0` circle. -/
noncomputable def q0q3CircleRayFarTime : ℝ :=
  q0q3CircleRayDot + Real.sqrt q0q3CircleRayDiscriminant

/-- Near intersection of `circle(Q0)` with the `Q3` ray. -/
noncomputable def q0q3CircleRayNearPoint : R2 :=
  karlssonOEISQ3.anchor +
    q0q3CircleRayNearTime • karlssonOEISQ3.rayDirection

/-- Far intersection of `circle(Q0)` with the `Q3` ray. -/
noncomputable def q0q3CircleRayFarPoint : R2 :=
  karlssonOEISQ3.anchor +
    q0q3CircleRayFarTime • karlssonOEISQ3.rayDirection

theorem q0q3CircleRayNearTime_nonneg :
    0 ≤ q0q3CircleRayNearTime := by
  unfold q0q3CircleRayNearTime
  nlinarith [q0q3CircleRay_sqrt_le_dot]

theorem q0q3CircleRayFarTime_nonneg :
    0 ≤ q0q3CircleRayFarTime := by
  unfold q0q3CircleRayFarTime
  nlinarith [q0q3CircleRayDot_pos,
    Real.sqrt_nonneg q0q3CircleRayDiscriminant]

private theorem q0q3CircleRayNearTime_quadratic :
    q0q3CircleRayNearTime ^ 2 -
        2 * q0q3CircleRayDot * q0q3CircleRayNearTime +
        q0q3CircleRayConstant = 0 := by
  unfold q0q3CircleRayNearTime q0q3CircleRayDiscriminant
  have hsqrt_sq :
      (Real.sqrt
          (q0q3CircleRayDot ^ 2 - q0q3CircleRayConstant)) ^ 2 =
        q0q3CircleRayDot ^ 2 - q0q3CircleRayConstant := by
    rw [Real.sq_sqrt]
    simpa [q0q3CircleRayDiscriminant] using
      q0q3CircleRayDiscriminant_nonneg
  nlinarith [hsqrt_sq]

private theorem q0q3CircleRayFarTime_quadratic :
    q0q3CircleRayFarTime ^ 2 -
        2 * q0q3CircleRayDot * q0q3CircleRayFarTime +
        q0q3CircleRayConstant = 0 := by
  unfold q0q3CircleRayFarTime q0q3CircleRayDiscriminant
  have hsqrt_sq :
      (Real.sqrt
          (q0q3CircleRayDot ^ 2 - q0q3CircleRayConstant)) ^ 2 =
        q0q3CircleRayDot ^ 2 - q0q3CircleRayConstant := by
    rw [Real.sq_sqrt]
    simpa [q0q3CircleRayDiscriminant] using
      q0q3CircleRayDiscriminant_nonneg
  nlinarith [hsqrt_sq]

private theorem q0q3CircleRayPoint_mem_q0_circle_of_quadratic
    {t : ℝ}
    (hquad :
      t ^ 2 - 2 * q0q3CircleRayDot * t +
          q0q3CircleRayConstant = 0) :
    karlssonOEISQ3.anchor + t • karlssonOEISQ3.rayDirection ∈
      circleSet karlssonOEISQ0.center karlssonOEISQ0.radius := by
  unfold q0q3CircleRayDot q0q3CircleRayConstant at hquad
  unfold circleSet
    TheoremOneEndToEnd.PaulsenLinearAlgebra.distSq2
    TheoremOneEndToEnd.PaulsenLinearAlgebra.normSq2
    TheoremOneEndToEnd.PaulsenLinearAlgebra.dot2
  simp [karlssonOEISQ0, karlssonOEISQ3, EuclideanLollipop.fromAnchor,
    angleDirection, point2, q3_theta_cos, q3_theta_sin]
  ring_nf at hquad ⊢
  have htrig :
      Real.sin (Real.pi * (1 / 30 : ℝ)) ^ 2 +
          Real.cos (Real.pi * (1 / 30 : ℝ)) ^ 2 = 1 := by
    exact Real.sin_sq_add_cos_sq (Real.pi * (1 / 30 : ℝ))
  nlinarith [htrig, hquad]

theorem q0q3CircleRayNearPoint_mem_q0_circle :
    q0q3CircleRayNearPoint ∈
      circleSet karlssonOEISQ0.center karlssonOEISQ0.radius := by
  unfold q0q3CircleRayNearPoint
  exact
    q0q3CircleRayPoint_mem_q0_circle_of_quadratic
      q0q3CircleRayNearTime_quadratic

theorem q0q3CircleRayFarPoint_mem_q0_circle :
    q0q3CircleRayFarPoint ∈
      circleSet karlssonOEISQ0.center karlssonOEISQ0.radius := by
  unfold q0q3CircleRayFarPoint
  exact
    q0q3CircleRayPoint_mem_q0_circle_of_quadratic
      q0q3CircleRayFarTime_quadratic

theorem q0q3CircleRayNearPoint_mem_q3_ray :
    q0q3CircleRayNearPoint ∈
      raySet karlssonOEISQ3.anchor karlssonOEISQ3.rayDirection := by
  exact ⟨q0q3CircleRayNearTime, q0q3CircleRayNearTime_nonneg, rfl⟩

theorem q0q3CircleRayFarPoint_mem_q3_ray :
    q0q3CircleRayFarPoint ∈
      raySet karlssonOEISQ3.anchor karlssonOEISQ3.rayDirection := by
  exact ⟨q0q3CircleRayFarTime, q0q3CircleRayFarTime_nonneg, rfl⟩

theorem q0q3CircleRayNearPoint_mem_euclideanCircleRaySet :
    toEuclideanR2 q0q3CircleRayNearPoint ∈
      euclideanCircleRaySet karlssonOEISQ0 karlssonOEISQ3 := by
  constructor
  · exact
      (mem_circleSet_iff_mem_euclideanSphere
        karlssonOEISQ0.radius_pos.le).1
        q0q3CircleRayNearPoint_mem_q0_circle
  · exact
      (mem_raySet_iff_mem_euclideanRaySet
        (p := q0q3CircleRayNearPoint)
        (anchor := karlssonOEISQ3.anchor)
        (direction := karlssonOEISQ3.rayDirection)).1
        q0q3CircleRayNearPoint_mem_q3_ray

theorem q0q3CircleRayFarPoint_mem_euclideanCircleRaySet :
    toEuclideanR2 q0q3CircleRayFarPoint ∈
      euclideanCircleRaySet karlssonOEISQ0 karlssonOEISQ3 := by
  constructor
  · exact
      (mem_circleSet_iff_mem_euclideanSphere
        karlssonOEISQ0.radius_pos.le).1
        q0q3CircleRayFarPoint_mem_q0_circle
  · exact
      (mem_raySet_iff_mem_euclideanRaySet
        (p := q0q3CircleRayFarPoint)
        (anchor := karlssonOEISQ3.anchor)
        (direction := karlssonOEISQ3.rayDirection)).1
        q0q3CircleRayFarPoint_mem_q3_ray

theorem q0q3CircleRayNearPoint_mem_base_pairIntersectionSet :
    q0q3CircleRayNearPoint ∈
      karlssonOEISBaseArrangement.pairIntersectionSet
        (0 : Fin 4) (3 : Fin 4) := by
  exact
    OEISSevenPoint.pair_mem_of_euclideanCircleRay
      (i := (0 : Fin 4)) (j := (3 : Fin 4))
      (p := q0q3CircleRayNearPoint)
      (by
        simpa [karlssonOEISBaseArrangement] using
          q0q3CircleRayNearPoint_mem_euclideanCircleRaySet)

theorem q0q3CircleRayFarPoint_mem_base_pairIntersectionSet :
    q0q3CircleRayFarPoint ∈
      karlssonOEISBaseArrangement.pairIntersectionSet
        (0 : Fin 4) (3 : Fin 4) := by
  exact
    OEISSevenPoint.pair_mem_of_euclideanCircleRay
      (i := (0 : Fin 4)) (j := (3 : Fin 4))
      (p := q0q3CircleRayFarPoint)
      (by
        simpa [karlssonOEISBaseArrangement] using
          q0q3CircleRayFarPoint_mem_euclideanCircleRaySet)


private abbrev q0q3CircleCircleDX : ℝ :=
  q0q3CenterX + 200

/-- Center displacement from `Q0`'s circle center to `Q3`'s circle center,
y-coordinate. -/
private abbrev q0q3CircleCircleDY : ℝ :=
  q0q3CenterY

/-- Squared distance between the two circle centers for `(Q0,Q3)`. -/
private abbrev q0q3CircleCircleD : ℝ :=
  q0q3CircleCircleDX ^ 2 + q0q3CircleCircleDY ^ 2

/-- Radical-axis dot coordinate for the two circle-circle intersections. -/
private abbrev q0q3CircleCircleA : ℝ :=
  (q0q3CircleCircleD + (30000 : ℝ)) / 2

/-- Squared perpendicular height of the two circle-circle intersections. -/
private abbrev q0q3CircleCircleH2 : ℝ :=
  (200 : ℝ) ^ 2 * q0q3CircleCircleD -
    q0q3CircleCircleA ^ 2

private theorem sin_beta_le_eight_div_fifteen :
    Real.sin beta ≤ (8 : ℝ) / 15 := by
  have hsin_le_beta : Real.sin beta ≤ beta :=
    Real.sin_le beta_pos.le
  have hbeta_le : beta ≤ (8 : ℝ) / 15 := by
    dsimp [beta]
    nlinarith [Real.pi_le_four]
  exact hsin_le_beta.trans hbeta_le

private theorem q0q3CircleCircleDX_gt_hundred :
    (100 : ℝ) < q0q3CircleCircleDX := by
  have hanchor_pos : 0 < karlssonOEISQ3AnchorX := by
    norm_num [karlssonOEISQ3AnchorX]
  unfold q0q3CircleCircleDX q0q3CenterX
  nlinarith [sin_beta_pos, hanchor_pos]

private theorem q0q3CircleCircleD_pos :
    0 < q0q3CircleCircleD := by
  unfold q0q3CircleCircleD
  nlinarith [q0q3CircleCircleDX_gt_hundred,
    sq_nonneg q0q3CircleCircleDY]

private theorem q0q3CircleCircleD_ne :
    q0q3CircleCircleD ≠ 0 :=
  q0q3CircleCircleD_pos.ne'

private theorem q0q3CircleCircleD_gt_ten_thousand :
    (10000 : ℝ) < q0q3CircleCircleD := by
  unfold q0q3CircleCircleD
  nlinarith [q0q3CircleCircleDX_gt_hundred,
    sq_nonneg q0q3CircleCircleDY]

private theorem q0q3CircleCircleD_gt_fifty_thousand :
    (50000 : ℝ) < q0q3CircleCircleD := by
  unfold q0q3CircleCircleD q0q3CircleCircleDX q0q3CircleCircleDY
    q0q3CenterX q0q3CenterY karlssonOEISQ3AnchorX
  nlinarith [thirteen_div_one_twenty_five_lt_sin_beta,
    nine_div_ten_lt_cos_beta]

private theorem q0q3CircleCircleD_lt_ninety_thousand :
    q0q3CircleCircleD < (90000 : ℝ) := by
  have hanchor_pos : 0 < karlssonOEISQ3AnchorX := by
    norm_num [karlssonOEISQ3AnchorX]
  have hanchor_lt_two : karlssonOEISQ3AnchorX < (2 : ℝ) := by
    norm_num [karlssonOEISQ3AnchorX]
  unfold q0q3CircleCircleD q0q3CircleCircleDX q0q3CircleCircleDY
    q0q3CenterX q0q3CenterY
  nlinarith [Real.sin_sq_add_cos_sq beta,
    sin_beta_le_eight_div_fifteen, Real.cos_le_one beta,
    sin_beta_pos, hanchor_pos, hanchor_lt_two]

/-- The private center-distance abbreviation is exactly the squared distance
between the `Q0` and `Q3` circle centers. -/
theorem q0q3CircleCircleD_eq_distSq2_centers :
    q0q3CircleCircleD =
      distSq2 karlssonOEISQ0.center karlssonOEISQ3.center := by
  rw [q0q3_q3_center_eq]
  simp [q0q3CircleCircleD, q0q3CircleCircleDX, q0q3CircleCircleDY,
    q0q3CenterX, q0q3CenterY, karlssonOEISQ0,
    EuclideanLollipop.fromAnchor, distSq2, normSq2, dot2, point2]
  ring

/-- The `Q0,Q3` circle pair satisfies Paulsen's strict obtuse-intersection
distance condition, hence is not intriguing. -/
theorem q0q3_circleObtuseCondition :
    TheoremOneEndToEnd.PaulsenLinearAlgebra.circleObtuseCondition
      karlssonOEISQ0.radius karlssonOEISQ3.radius
      karlssonOEISQ0.center karlssonOEISQ3.center := by
  unfold TheoremOneEndToEnd.PaulsenLinearAlgebra.circleObtuseCondition
  constructor
  · rw [← q0q3CircleCircleD_eq_distSq2_centers]
    have hrad :
        karlssonOEISQ0.radius ^ 2 + karlssonOEISQ3.radius ^ 2 =
          (50000 : ℝ) := by
      norm_num [karlssonOEISQ0, karlssonOEISQ3,
        EuclideanLollipop.fromAnchor]
    rw [hrad]
    exact q0q3CircleCircleD_gt_fifty_thousand
  · rw [← q0q3CircleCircleD_eq_distSq2_centers]
    have hsum :
        (karlssonOEISQ0.radius + karlssonOEISQ3.radius) ^ 2 =
          (90000 : ℝ) := by
      norm_num [karlssonOEISQ0, karlssonOEISQ3,
        EuclideanLollipop.fromAnchor]
    rw [hsum]
    exact q0q3CircleCircleD_lt_ninety_thousand

/-- Pair-level form: `(Q0,Q3)` is not intriguing. -/
theorem q0q3_not_circleIntriguingPair :
    ¬ TheoremOneEndToEnd.PaulsenLinearAlgebra.circleIntriguingPair
      karlssonOEISQ0.radius karlssonOEISQ3.radius
      karlssonOEISQ0.center karlssonOEISQ3.center := by
  classical
  exact not_not.mpr q0q3_circleObtuseCondition

private theorem q0q3CircleCircleH2_pos :
    0 < q0q3CircleCircleH2 := by
  unfold q0q3CircleCircleH2 q0q3CircleCircleA
  have hprod :
      0 <
        ((90000 : ℝ) - q0q3CircleCircleD) *
          (q0q3CircleCircleD - (10000 : ℝ)) :=
    mul_pos (sub_pos.2 q0q3CircleCircleD_lt_ninety_thousand)
      (sub_pos.2 q0q3CircleCircleD_gt_ten_thousand)
  nlinarith [hprod]

private theorem q0q3CircleCircleH2_nonneg :
    0 ≤ q0q3CircleCircleH2 :=
  q0q3CircleCircleH2_pos.le

/-- One of the two intersections of `circle(Q0)` and `circle(Q3)`. -/
noncomputable def q0q3CircleCircleUpperPoint : R2 :=
  point2
    (-(200 : ℝ) +
      (q0q3CircleCircleA * q0q3CircleCircleDX -
        Real.sqrt q0q3CircleCircleH2 * q0q3CircleCircleDY) /
        q0q3CircleCircleD)
    ((q0q3CircleCircleA * q0q3CircleCircleDY +
        Real.sqrt q0q3CircleCircleH2 * q0q3CircleCircleDX) /
        q0q3CircleCircleD)

/-- The other intersection of `circle(Q0)` and `circle(Q3)`. -/
noncomputable def q0q3CircleCircleLowerPoint : R2 :=
  point2
    (-(200 : ℝ) +
      (q0q3CircleCircleA * q0q3CircleCircleDX +
        Real.sqrt q0q3CircleCircleH2 * q0q3CircleCircleDY) /
        q0q3CircleCircleD)
    ((q0q3CircleCircleA * q0q3CircleCircleDY -
        Real.sqrt q0q3CircleCircleH2 * q0q3CircleCircleDX) /
        q0q3CircleCircleD)

private theorem q0q3CircleCircle_sqrt_sq :
    (Real.sqrt q0q3CircleCircleH2) ^ 2 =
      q0q3CircleCircleH2 :=
  Real.sq_sqrt q0q3CircleCircleH2_nonneg

private theorem q0q3CircleCircle_A_sq_add_H_sq_q0 :
    q0q3CircleCircleA ^ 2 +
        (Real.sqrt q0q3CircleCircleH2) ^ 2 =
      (200 : ℝ) ^ 2 * q0q3CircleCircleD := by
  rw [q0q3CircleCircle_sqrt_sq]
  unfold q0q3CircleCircleH2
  ring

private theorem q0q3CircleCircle_A_sub_D_sq_add_H_sq_q3 :
    (q0q3CircleCircleA - q0q3CircleCircleD) ^ 2 +
        (Real.sqrt q0q3CircleCircleH2) ^ 2 =
      (100 : ℝ) ^ 2 * q0q3CircleCircleD := by
  rw [q0q3CircleCircle_sqrt_sq]
  unfold q0q3CircleCircleH2 q0q3CircleCircleA
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

private theorem circleCircleUpper_q3_algebra
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

private theorem circleCircleLower_q3_algebra
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

private theorem q0q3CircleCircleUpper_q0_coordinate :
    ((q0q3CircleCircleA * q0q3CircleCircleDX -
          Real.sqrt q0q3CircleCircleH2 * q0q3CircleCircleDY) /
        q0q3CircleCircleD) *
        ((q0q3CircleCircleA * q0q3CircleCircleDX -
            Real.sqrt q0q3CircleCircleH2 * q0q3CircleCircleDY) /
          q0q3CircleCircleD) +
      ((q0q3CircleCircleA * q0q3CircleCircleDY +
          Real.sqrt q0q3CircleCircleH2 * q0q3CircleCircleDX) /
        q0q3CircleCircleD) *
        ((q0q3CircleCircleA * q0q3CircleCircleDY +
            Real.sqrt q0q3CircleCircleH2 * q0q3CircleCircleDX) /
          q0q3CircleCircleD) =
      (200 : ℝ) ^ 2 := by
  exact circleCircleUpper_q0_algebra
    q0q3CircleCircleDX q0q3CircleCircleDY q0q3CircleCircleD
    q0q3CircleCircleA (Real.sqrt q0q3CircleCircleH2)
    rfl q0q3CircleCircle_A_sq_add_H_sq_q0 q0q3CircleCircleD_ne

private theorem q0q3CircleCircleLower_q0_coordinate :
    ((q0q3CircleCircleA * q0q3CircleCircleDX +
          Real.sqrt q0q3CircleCircleH2 * q0q3CircleCircleDY) /
        q0q3CircleCircleD) *
        ((q0q3CircleCircleA * q0q3CircleCircleDX +
            Real.sqrt q0q3CircleCircleH2 * q0q3CircleCircleDY) /
          q0q3CircleCircleD) +
      ((q0q3CircleCircleA * q0q3CircleCircleDY -
          Real.sqrt q0q3CircleCircleH2 * q0q3CircleCircleDX) /
        q0q3CircleCircleD) *
        ((q0q3CircleCircleA * q0q3CircleCircleDY -
            Real.sqrt q0q3CircleCircleH2 * q0q3CircleCircleDX) /
          q0q3CircleCircleD) =
      (200 : ℝ) ^ 2 := by
  exact circleCircleLower_q0_algebra
    q0q3CircleCircleDX q0q3CircleCircleDY q0q3CircleCircleD
    q0q3CircleCircleA (Real.sqrt q0q3CircleCircleH2)
    rfl q0q3CircleCircle_A_sq_add_H_sq_q0 q0q3CircleCircleD_ne

private theorem q0q3CircleCircleUpper_q3_coordinate :
    (-(200 : ℝ) +
          (q0q3CircleCircleA * q0q3CircleCircleDX -
              Real.sqrt q0q3CircleCircleH2 * q0q3CircleCircleDY) /
            q0q3CircleCircleD -
        q0q3CenterX) *
        (-(200 : ℝ) +
            (q0q3CircleCircleA * q0q3CircleCircleDX -
                Real.sqrt q0q3CircleCircleH2 * q0q3CircleCircleDY) /
              q0q3CircleCircleD -
          q0q3CenterX) +
      ((q0q3CircleCircleA * q0q3CircleCircleDY +
            Real.sqrt q0q3CircleCircleH2 * q0q3CircleCircleDX) /
          q0q3CircleCircleD -
        q0q3CenterY) *
        ((q0q3CircleCircleA * q0q3CircleCircleDY +
              Real.sqrt q0q3CircleCircleH2 * q0q3CircleCircleDX) /
            q0q3CircleCircleD -
          q0q3CenterY) =
      (100 : ℝ) ^ 2 := by
  exact circleCircleUpper_q3_algebra
    q0q3CircleCircleDX q0q3CircleCircleDY q0q3CircleCircleD
    q0q3CircleCircleA (Real.sqrt q0q3CircleCircleH2)
    q0q3CenterX q0q3CenterY rfl rfl rfl
    q0q3CircleCircle_A_sub_D_sq_add_H_sq_q3 q0q3CircleCircleD_ne

private theorem q0q3CircleCircleLower_q3_coordinate :
    (-(200 : ℝ) +
          (q0q3CircleCircleA * q0q3CircleCircleDX +
              Real.sqrt q0q3CircleCircleH2 * q0q3CircleCircleDY) /
            q0q3CircleCircleD -
        q0q3CenterX) *
        (-(200 : ℝ) +
            (q0q3CircleCircleA * q0q3CircleCircleDX +
                Real.sqrt q0q3CircleCircleH2 * q0q3CircleCircleDY) /
              q0q3CircleCircleD -
          q0q3CenterX) +
      ((q0q3CircleCircleA * q0q3CircleCircleDY -
            Real.sqrt q0q3CircleCircleH2 * q0q3CircleCircleDX) /
          q0q3CircleCircleD -
        q0q3CenterY) *
        ((q0q3CircleCircleA * q0q3CircleCircleDY -
              Real.sqrt q0q3CircleCircleH2 * q0q3CircleCircleDX) /
            q0q3CircleCircleD -
          q0q3CenterY) =
      (100 : ℝ) ^ 2 := by
  exact circleCircleLower_q3_algebra
    q0q3CircleCircleDX q0q3CircleCircleDY q0q3CircleCircleD
    q0q3CircleCircleA (Real.sqrt q0q3CircleCircleH2)
    q0q3CenterX q0q3CenterY rfl rfl rfl
    q0q3CircleCircle_A_sub_D_sq_add_H_sq_q3 q0q3CircleCircleD_ne

theorem q0q3CircleCircleUpperPoint_mem_q0_circle :
    q0q3CircleCircleUpperPoint ∈
      circleSet karlssonOEISQ0.center karlssonOEISQ0.radius := by
  unfold q0q3CircleCircleUpperPoint circleSet
    TheoremOneEndToEnd.PaulsenLinearAlgebra.distSq2
    TheoremOneEndToEnd.PaulsenLinearAlgebra.normSq2
    TheoremOneEndToEnd.PaulsenLinearAlgebra.dot2
  simp [karlssonOEISQ0, EuclideanLollipop.fromAnchor, angleDirection,
    point2]
  exact q0q3CircleCircleUpper_q0_coordinate

theorem q0q3CircleCircleLowerPoint_mem_q0_circle :
    q0q3CircleCircleLowerPoint ∈
      circleSet karlssonOEISQ0.center karlssonOEISQ0.radius := by
  unfold q0q3CircleCircleLowerPoint circleSet
    TheoremOneEndToEnd.PaulsenLinearAlgebra.distSq2
    TheoremOneEndToEnd.PaulsenLinearAlgebra.normSq2
    TheoremOneEndToEnd.PaulsenLinearAlgebra.dot2
  simp [karlssonOEISQ0, EuclideanLollipop.fromAnchor, angleDirection,
    point2]
  exact q0q3CircleCircleLower_q0_coordinate

theorem q0q3CircleCircleUpperPoint_mem_q3_circle :
    q0q3CircleCircleUpperPoint ∈
      circleSet karlssonOEISQ3.center karlssonOEISQ3.radius := by
  unfold q0q3CircleCircleUpperPoint circleSet
    TheoremOneEndToEnd.PaulsenLinearAlgebra.distSq2
    TheoremOneEndToEnd.PaulsenLinearAlgebra.normSq2
    TheoremOneEndToEnd.PaulsenLinearAlgebra.dot2
  rw [q0q3_q3_center_eq]
  simp [karlssonOEISQ3, EuclideanLollipop.fromAnchor, point2]
  exact q0q3CircleCircleUpper_q3_coordinate

theorem q0q3CircleCircleLowerPoint_mem_q3_circle :
    q0q3CircleCircleLowerPoint ∈
      circleSet karlssonOEISQ3.center karlssonOEISQ3.radius := by
  unfold q0q3CircleCircleLowerPoint circleSet
    TheoremOneEndToEnd.PaulsenLinearAlgebra.distSq2
    TheoremOneEndToEnd.PaulsenLinearAlgebra.normSq2
    TheoremOneEndToEnd.PaulsenLinearAlgebra.dot2
  rw [q0q3_q3_center_eq]
  simp [karlssonOEISQ3, EuclideanLollipop.fromAnchor, point2]
  exact q0q3CircleCircleLower_q3_coordinate

theorem q0q3CircleCircleUpperPoint_mem_euclideanCircleCircleSet :
    toEuclideanR2 q0q3CircleCircleUpperPoint ∈
      euclideanCircleCircleSet karlssonOEISQ0 karlssonOEISQ3 := by
  constructor
  · exact
      (mem_circleSet_iff_mem_euclideanSphere
        karlssonOEISQ0.radius_pos.le).1
        q0q3CircleCircleUpperPoint_mem_q0_circle
  · exact
      (mem_circleSet_iff_mem_euclideanSphere
        karlssonOEISQ3.radius_pos.le).1
        q0q3CircleCircleUpperPoint_mem_q3_circle

theorem q0q3CircleCircleLowerPoint_mem_euclideanCircleCircleSet :
    toEuclideanR2 q0q3CircleCircleLowerPoint ∈
      euclideanCircleCircleSet karlssonOEISQ0 karlssonOEISQ3 := by
  constructor
  · exact
      (mem_circleSet_iff_mem_euclideanSphere
        karlssonOEISQ0.radius_pos.le).1
        q0q3CircleCircleLowerPoint_mem_q0_circle
  · exact
      (mem_circleSet_iff_mem_euclideanSphere
        karlssonOEISQ3.radius_pos.le).1
        q0q3CircleCircleLowerPoint_mem_q3_circle

theorem q0q3CircleCircleUpperPoint_mem_base_pairIntersectionSet :
    q0q3CircleCircleUpperPoint ∈
      karlssonOEISBaseArrangement.pairIntersectionSet
        (0 : Fin 4) (3 : Fin 4) := by
  exact
    OEISSevenPoint.pair_mem_of_euclideanCircleCircle
      (i := (0 : Fin 4)) (j := (3 : Fin 4))
      (p := q0q3CircleCircleUpperPoint)
      (by
        simpa [karlssonOEISBaseArrangement] using
          q0q3CircleCircleUpperPoint_mem_euclideanCircleCircleSet)

theorem q0q3CircleCircleLowerPoint_mem_base_pairIntersectionSet :
    q0q3CircleCircleLowerPoint ∈
      karlssonOEISBaseArrangement.pairIntersectionSet
        (0 : Fin 4) (3 : Fin 4) := by
  exact
    OEISSevenPoint.pair_mem_of_euclideanCircleCircle
      (i := (0 : Fin 4)) (j := (3 : Fin 4))
      (p := q0q3CircleCircleLowerPoint)
      (by
        simpa [karlssonOEISBaseArrangement] using
          q0q3CircleCircleLowerPoint_mem_euclideanCircleCircleSet)


private theorem q0q3Center_dist_sq_gt_hundred_sq :
    (100 : ℝ) ^ 2 < q0q3CenterX ^ 2 + q0q3CenterY ^ 2 := by
  have hanchor_pos : 0 < karlssonOEISQ3AnchorX := by
    norm_num [karlssonOEISQ3AnchorX]
  unfold q0q3CenterX q0q3CenterY
  nlinarith [Real.sin_sq_add_cos_sq beta, sin_beta_pos, cos_beta_pos,
    hanchor_pos]

private theorem q0q3RayCircleDiscriminant_lt_centerX_sq :
    q0q3RayCircleDiscriminant < q0q3CenterX ^ 2 := by
  unfold q0q3RayCircleDiscriminant
  nlinarith [q0q3Center_dist_sq_gt_hundred_sq]

private theorem q0q3RayCircle_sqrt_lt_centerX :
    Real.sqrt q0q3RayCircleDiscriminant < q0q3CenterX := by
  rw [Real.sqrt_lt q0q3RayCircleDiscriminant_nonneg
    q0q3CenterX_pos.le]
  exact q0q3RayCircleDiscriminant_lt_centerX_sq

private theorem q0q3RayCircle_sqrt_pos :
    0 < Real.sqrt q0q3RayCircleDiscriminant :=
  Real.sqrt_pos.2 q0q3RayCircleDiscriminant_pos

theorem q0q3RayCircleLeftPoint_x_pos :
    0 < q0q3RayCircleLeftPoint 0 := by
  unfold q0q3RayCircleLeftPoint
  simp [point2]
  nlinarith [q0q3RayCircle_sqrt_lt_centerX]

theorem q0q3RayCircleRightPoint_x_pos :
    0 < q0q3RayCircleRightPoint 0 := by
  unfold q0q3RayCircleRightPoint
  simp [point2]
  nlinarith [q0q3CenterX_pos, q0q3RayCircle_sqrt_pos]

theorem q0q3RayCircleLeftPoint_y_eq_zero :
    q0q3RayCircleLeftPoint 1 = 0 := by
  simp [q0q3RayCircleLeftPoint, point2]

theorem q0q3RayCircleRightPoint_y_eq_zero :
    q0q3RayCircleRightPoint 1 = 0 := by
  simp [q0q3RayCircleRightPoint, point2]

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

theorem q0q3RayCircleLeftPoint_not_mem_q0_circle :
    q0q3RayCircleLeftPoint ∉
      circleSet karlssonOEISQ0.center karlssonOEISQ0.radius :=
  q0_xaxis_pos_not_mem_q0_circle
    q0q3RayCircleLeftPoint_x_pos q0q3RayCircleLeftPoint_y_eq_zero

theorem q0q3RayCircleRightPoint_not_mem_q0_circle :
    q0q3RayCircleRightPoint ∉
      circleSet karlssonOEISQ0.center karlssonOEISQ0.radius :=
  q0_xaxis_pos_not_mem_q0_circle
    q0q3RayCircleRightPoint_x_pos q0q3RayCircleRightPoint_y_eq_zero

theorem q0q3RayRayPoint_not_mem_q0_circle :
    q0q3RayRayPoint ∉
      circleSet karlssonOEISQ0.center karlssonOEISQ0.radius :=
  q0_xaxis_pos_not_mem_q0_circle
    q0q3RayRayPoint_x_pos q0q3RayRayPoint_y_eq_zero

private theorem q3_ray_point_not_mem_q3_circle_of_time_pos
    {t : ℝ} (ht : 0 < t) :
    karlssonOEISQ3.anchor + t • karlssonOEISQ3.rayDirection ∉
      circleSet karlssonOEISQ3.center karlssonOEISQ3.radius := by
  intro hp
  unfold circleSet
    TheoremOneEndToEnd.PaulsenLinearAlgebra.distSq2
    TheoremOneEndToEnd.PaulsenLinearAlgebra.normSq2
    TheoremOneEndToEnd.PaulsenLinearAlgebra.dot2 at hp
  simp [karlssonOEISQ3, EuclideanLollipop.fromAnchor, angleDirection,
    point2, q3_theta_cos, q3_theta_sin] at hp
  ring_nf at hp
  have htrig :
      Real.sin (Real.pi * (1 / 30 : ℝ)) ^ 2 +
          Real.cos (Real.pi * (1 / 30 : ℝ)) ^ 2 = 1 := by
    exact Real.sin_sq_add_cos_sq (Real.pi * (1 / 30 : ℝ))
  nlinarith [htrig, ht, hp]

private theorem q0q3CircleRay_sqrt_lt_dot :
    Real.sqrt q0q3CircleRayDiscriminant < q0q3CircleRayDot := by
  rw [Real.sqrt_lt q0q3CircleRayDiscriminant_nonneg
    q0q3CircleRayDot_pos.le]
  unfold q0q3CircleRayDiscriminant
  nlinarith [q0q3CircleRayConstant_pos]

theorem q0q3CircleRayNearTime_pos :
    0 < q0q3CircleRayNearTime := by
  unfold q0q3CircleRayNearTime
  nlinarith [q0q3CircleRay_sqrt_lt_dot]

theorem q0q3CircleRayFarTime_pos :
    0 < q0q3CircleRayFarTime := by
  unfold q0q3CircleRayFarTime
  nlinarith [q0q3CircleRayDot_pos,
    Real.sqrt_nonneg q0q3CircleRayDiscriminant]

theorem q0q3CircleRayNearPoint_not_mem_q3_circle :
    q0q3CircleRayNearPoint ∉
      circleSet karlssonOEISQ3.center karlssonOEISQ3.radius := by
  unfold q0q3CircleRayNearPoint
  exact
    q3_ray_point_not_mem_q3_circle_of_time_pos
      q0q3CircleRayNearTime_pos

theorem q0q3CircleRayFarPoint_not_mem_q3_circle :
    q0q3CircleRayFarPoint ∉
      circleSet karlssonOEISQ3.center karlssonOEISQ3.radius := by
  unfold q0q3CircleRayFarPoint
  exact
    q3_ray_point_not_mem_q3_circle_of_time_pos
      q0q3CircleRayFarTime_pos

theorem q0q3RayRayPoint_not_mem_q3_circle :
    q0q3RayRayPoint ∉
      circleSet karlssonOEISQ3.center karlssonOEISQ3.radius := by
  unfold q0q3RayRayPoint
  exact
    q3_ray_point_not_mem_q3_circle_of_time_pos
      q0q3RayRayTime_pos

theorem q0q3CircleCircleUpperPoint_ne_lower :
    q0q3CircleCircleUpperPoint ≠ q0q3CircleCircleLowerPoint := by
  intro h
  have hy := congr_fun h 1
  unfold q0q3CircleCircleUpperPoint q0q3CircleCircleLowerPoint at hy
  simp [point2] at hy
  change
    (q0q3CircleCircleA * q0q3CircleCircleDY +
          Real.sqrt q0q3CircleCircleH2 * q0q3CircleCircleDX) /
        q0q3CircleCircleD =
      (q0q3CircleCircleA * q0q3CircleCircleDY -
          Real.sqrt q0q3CircleCircleH2 * q0q3CircleCircleDX) /
        q0q3CircleCircleD at hy
  have hH : 0 < Real.sqrt q0q3CircleCircleH2 :=
    Real.sqrt_pos.2 q0q3CircleCircleH2_pos
  have hDX : 0 < q0q3CircleCircleDX := by
    nlinarith [q0q3CircleCircleDX_gt_hundred]
  have hdiff :
      ((q0q3CircleCircleA * q0q3CircleCircleDY +
            Real.sqrt q0q3CircleCircleH2 * q0q3CircleCircleDX) /
          q0q3CircleCircleD) -
        ((q0q3CircleCircleA * q0q3CircleCircleDY -
            Real.sqrt q0q3CircleCircleH2 * q0q3CircleCircleDX) /
          q0q3CircleCircleD) = 0 := by
    exact sub_eq_zero.2 hy
  have hdiff_eval :
      ((q0q3CircleCircleA * q0q3CircleCircleDY +
            Real.sqrt q0q3CircleCircleH2 * q0q3CircleCircleDX) /
          q0q3CircleCircleD) -
        ((q0q3CircleCircleA * q0q3CircleCircleDY -
            Real.sqrt q0q3CircleCircleH2 * q0q3CircleCircleDX) /
          q0q3CircleCircleD) =
        (2 * Real.sqrt q0q3CircleCircleH2 *
            q0q3CircleCircleDX) / q0q3CircleCircleD := by
    field_simp [q0q3CircleCircleD_ne]
    ring
  have hpos :
      0 <
        (2 * Real.sqrt q0q3CircleCircleH2 *
            q0q3CircleCircleDX) / q0q3CircleCircleD := by
    exact div_pos (mul_pos (mul_pos (by norm_num) hH) hDX)
      q0q3CircleCircleD_pos
  rw [hdiff_eval] at hdiff
  nlinarith

theorem q0q3CircleRayNearPoint_ne_far :
    q0q3CircleRayNearPoint ≠ q0q3CircleRayFarPoint := by
  intro h
  have hy := congr_fun h 1
  unfold q0q3CircleRayNearPoint q0q3CircleRayFarPoint
    q0q3CircleRayNearTime q0q3CircleRayFarTime at hy
  simp [karlssonOEISQ3, EuclideanLollipop.fromAnchor, angleDirection,
    point2, q3_theta_sin] at hy
  have hsqrt : 0 < Real.sqrt q0q3CircleRayDiscriminant :=
    Real.sqrt_pos.2 q0q3CircleRayDiscriminant_pos
  rcases hy with htime | hcos
  · nlinarith [hsqrt, htime]
  · exact cos_beta_pos.ne' hcos

theorem q0q3RayCircleLeftPoint_ne_right :
    q0q3RayCircleLeftPoint ≠ q0q3RayCircleRightPoint := by
  intro h
  have hx := congr_fun h 0
  unfold q0q3RayCircleLeftPoint q0q3RayCircleRightPoint at hx
  simp [point2] at hx
  nlinarith [q0q3RayCircle_sqrt_pos]

private theorem ne_of_left_mem_q0_circle_of_right_not_mem_q0_circle
    {p q : R2}
    (hp : p ∈ circleSet karlssonOEISQ0.center karlssonOEISQ0.radius)
    (hq : q ∉ circleSet karlssonOEISQ0.center karlssonOEISQ0.radius) :
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

theorem q0q3CircleCircleUpperPoint_ne_circleRayNear :
    q0q3CircleCircleUpperPoint ≠ q0q3CircleRayNearPoint :=
  ne_of_left_mem_q3_circle_of_right_not_mem_q3_circle
    q0q3CircleCircleUpperPoint_mem_q3_circle
    q0q3CircleRayNearPoint_not_mem_q3_circle

theorem q0q3CircleCircleUpperPoint_ne_circleRayFar :
    q0q3CircleCircleUpperPoint ≠ q0q3CircleRayFarPoint :=
  ne_of_left_mem_q3_circle_of_right_not_mem_q3_circle
    q0q3CircleCircleUpperPoint_mem_q3_circle
    q0q3CircleRayFarPoint_not_mem_q3_circle

theorem q0q3CircleCircleLowerPoint_ne_circleRayNear :
    q0q3CircleCircleLowerPoint ≠ q0q3CircleRayNearPoint :=
  ne_of_left_mem_q3_circle_of_right_not_mem_q3_circle
    q0q3CircleCircleLowerPoint_mem_q3_circle
    q0q3CircleRayNearPoint_not_mem_q3_circle

theorem q0q3CircleCircleLowerPoint_ne_circleRayFar :
    q0q3CircleCircleLowerPoint ≠ q0q3CircleRayFarPoint :=
  ne_of_left_mem_q3_circle_of_right_not_mem_q3_circle
    q0q3CircleCircleLowerPoint_mem_q3_circle
    q0q3CircleRayFarPoint_not_mem_q3_circle

theorem q0q3CircleCircleUpperPoint_ne_rayCircleLeft :
    q0q3CircleCircleUpperPoint ≠ q0q3RayCircleLeftPoint :=
  ne_of_left_mem_q0_circle_of_right_not_mem_q0_circle
    q0q3CircleCircleUpperPoint_mem_q0_circle
    q0q3RayCircleLeftPoint_not_mem_q0_circle

theorem q0q3CircleCircleUpperPoint_ne_rayCircleRight :
    q0q3CircleCircleUpperPoint ≠ q0q3RayCircleRightPoint :=
  ne_of_left_mem_q0_circle_of_right_not_mem_q0_circle
    q0q3CircleCircleUpperPoint_mem_q0_circle
    q0q3RayCircleRightPoint_not_mem_q0_circle

theorem q0q3CircleCircleUpperPoint_ne_rayRay :
    q0q3CircleCircleUpperPoint ≠ q0q3RayRayPoint :=
  ne_of_left_mem_q0_circle_of_right_not_mem_q0_circle
    q0q3CircleCircleUpperPoint_mem_q0_circle
    q0q3RayRayPoint_not_mem_q0_circle

theorem q0q3CircleCircleLowerPoint_ne_rayCircleLeft :
    q0q3CircleCircleLowerPoint ≠ q0q3RayCircleLeftPoint :=
  ne_of_left_mem_q0_circle_of_right_not_mem_q0_circle
    q0q3CircleCircleLowerPoint_mem_q0_circle
    q0q3RayCircleLeftPoint_not_mem_q0_circle

theorem q0q3CircleCircleLowerPoint_ne_rayCircleRight :
    q0q3CircleCircleLowerPoint ≠ q0q3RayCircleRightPoint :=
  ne_of_left_mem_q0_circle_of_right_not_mem_q0_circle
    q0q3CircleCircleLowerPoint_mem_q0_circle
    q0q3RayCircleRightPoint_not_mem_q0_circle

theorem q0q3CircleCircleLowerPoint_ne_rayRay :
    q0q3CircleCircleLowerPoint ≠ q0q3RayRayPoint :=
  ne_of_left_mem_q0_circle_of_right_not_mem_q0_circle
    q0q3CircleCircleLowerPoint_mem_q0_circle
    q0q3RayRayPoint_not_mem_q0_circle

theorem q0q3CircleRayNearPoint_ne_rayCircleLeft :
    q0q3CircleRayNearPoint ≠ q0q3RayCircleLeftPoint :=
  ne_of_left_mem_q0_circle_of_right_not_mem_q0_circle
    q0q3CircleRayNearPoint_mem_q0_circle
    q0q3RayCircleLeftPoint_not_mem_q0_circle

theorem q0q3CircleRayNearPoint_ne_rayCircleRight :
    q0q3CircleRayNearPoint ≠ q0q3RayCircleRightPoint :=
  ne_of_left_mem_q0_circle_of_right_not_mem_q0_circle
    q0q3CircleRayNearPoint_mem_q0_circle
    q0q3RayCircleRightPoint_not_mem_q0_circle

theorem q0q3CircleRayNearPoint_ne_rayRay :
    q0q3CircleRayNearPoint ≠ q0q3RayRayPoint :=
  ne_of_left_mem_q0_circle_of_right_not_mem_q0_circle
    q0q3CircleRayNearPoint_mem_q0_circle
    q0q3RayRayPoint_not_mem_q0_circle

theorem q0q3CircleRayFarPoint_ne_rayCircleLeft :
    q0q3CircleRayFarPoint ≠ q0q3RayCircleLeftPoint :=
  ne_of_left_mem_q0_circle_of_right_not_mem_q0_circle
    q0q3CircleRayFarPoint_mem_q0_circle
    q0q3RayCircleLeftPoint_not_mem_q0_circle

theorem q0q3CircleRayFarPoint_ne_rayCircleRight :
    q0q3CircleRayFarPoint ≠ q0q3RayCircleRightPoint :=
  ne_of_left_mem_q0_circle_of_right_not_mem_q0_circle
    q0q3CircleRayFarPoint_mem_q0_circle
    q0q3RayCircleRightPoint_not_mem_q0_circle

theorem q0q3CircleRayFarPoint_ne_rayRay :
    q0q3CircleRayFarPoint ≠ q0q3RayRayPoint :=
  ne_of_left_mem_q0_circle_of_right_not_mem_q0_circle
    q0q3CircleRayFarPoint_mem_q0_circle
    q0q3RayRayPoint_not_mem_q0_circle

theorem q0q3RayCircleLeftPoint_ne_rayRay :
    q0q3RayCircleLeftPoint ≠ q0q3RayRayPoint :=
  ne_of_left_mem_q3_circle_of_right_not_mem_q3_circle
    q0q3RayCircleLeftPoint_mem_q3_circle
    q0q3RayRayPoint_not_mem_q3_circle

theorem q0q3RayCircleRightPoint_ne_rayRay :
    q0q3RayCircleRightPoint ≠ q0q3RayRayPoint :=
  ne_of_left_mem_q3_circle_of_right_not_mem_q3_circle
    q0q3RayCircleRightPoint_mem_q3_circle
    q0q3RayRayPoint_not_mem_q3_circle

/-- The seven explicit labelled component points for `(Q0,Q3)`. -/
noncomputable def q0q3SevenPointFinset : Finset R2 :=
  {q0q3CircleCircleUpperPoint, q0q3CircleCircleLowerPoint,
    q0q3CircleRayNearPoint, q0q3CircleRayFarPoint,
    q0q3RayCircleLeftPoint, q0q3RayCircleRightPoint,
    q0q3RayRayPoint}

theorem q0q3SevenPointFinset_card :
    q0q3SevenPointFinset.card = 7 := by
  classical
  simp [q0q3SevenPointFinset,
    q0q3CircleCircleUpperPoint_ne_lower,
    q0q3CircleCircleUpperPoint_ne_circleRayNear,
    q0q3CircleCircleUpperPoint_ne_circleRayFar,
    q0q3CircleCircleUpperPoint_ne_rayCircleLeft,
    q0q3CircleCircleUpperPoint_ne_rayCircleRight,
    q0q3CircleCircleUpperPoint_ne_rayRay,
    q0q3CircleCircleLowerPoint_ne_circleRayNear,
    q0q3CircleCircleLowerPoint_ne_circleRayFar,
    q0q3CircleCircleLowerPoint_ne_rayCircleLeft,
    q0q3CircleCircleLowerPoint_ne_rayCircleRight,
    q0q3CircleCircleLowerPoint_ne_rayRay,
    q0q3CircleRayNearPoint_ne_far,
    q0q3CircleRayNearPoint_ne_rayCircleLeft,
    q0q3CircleRayNearPoint_ne_rayCircleRight,
    q0q3CircleRayNearPoint_ne_rayRay,
    q0q3CircleRayFarPoint_ne_rayCircleLeft,
    q0q3CircleRayFarPoint_ne_rayCircleRight,
    q0q3CircleRayFarPoint_ne_rayRay,
    q0q3RayCircleLeftPoint_ne_right,
    q0q3RayCircleLeftPoint_ne_rayRay,
    q0q3RayCircleRightPoint_ne_rayRay]

theorem q0q3SevenPointFinset_subset :
    ∀ p ∈ q0q3SevenPointFinset,
      p ∈ karlssonOEISBaseArrangement.pairIntersectionSet
        (0 : Fin 4) (3 : Fin 4) := by
  intro p hp
  simp [q0q3SevenPointFinset] at hp
  rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact q0q3CircleCircleUpperPoint_mem_base_pairIntersectionSet
  · exact q0q3CircleCircleLowerPoint_mem_base_pairIntersectionSet
  · exact q0q3CircleRayNearPoint_mem_base_pairIntersectionSet
  · exact q0q3CircleRayFarPoint_mem_base_pairIntersectionSet
  · exact q0q3RayCircleLeftPoint_mem_base_pairIntersectionSet
  · exact q0q3RayCircleRightPoint_mem_base_pairIntersectionSet
  · exact q0q3RayRayPoint_mem_base_pairIntersectionSet

/-- Seven-point lower witness for the exact OEIS base pair `(Q0,Q3)`. -/
noncomputable def q0q3SevenPointSubset :
    OEISSevenPoint.SevenPointSubset (0 : Fin 4) (3 : Fin 4) where
  points := q0q3SevenPointFinset
  card_eq_seven := q0q3SevenPointFinset_card
  points_subset := q0q3SevenPointFinset_subset

/-- Exact pair-coordinate crossing certificate for `(Q0,Q3)`. -/
noncomputable def q0q3PairCoordinateCrossingCertificate :
    KarlssonOEISBasePairCoordinateCrossingCertificate
      (0 : Fin 4) (3 : Fin 4) (by decide) :=
  OEISSevenPoint.pair03Certificate q0q3SevenPointSubset


end

end OEISPair03
end CompleteFormalization
end TheoremOneManuscript
end Lollipop
