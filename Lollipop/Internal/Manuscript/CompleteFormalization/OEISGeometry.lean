import Lollipop.Internal.Manuscript.ExplicitInputs.KarlssonOEISGeometry
import Mathlib.Analysis.Real.Sqrt
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds

/-!
Additional exact OEIS/Karlsson coordinate facts for the complete
formalization endpoint.

This file stays in the new `CompleteFormalization` folder.  It completes the
exact finite carrier-intersection analysis for the exceptional base pair
`(Q0,Q1)`, including the explicitly named ray-ray intersection point.
-/

namespace Lollipop
namespace TheoremOneManuscript
namespace CompleteFormalization

open PrimitiveGeometry

namespace OEISGeometry

noncomputable section

open ExplicitInputs

private abbrev theta : ℝ := (1 : ℝ) / 100

/-- Forward time along the `Q1` ray until it reaches the `Q0` ray's
supporting x-axis. -/
noncomputable def q0q1RayRayTime : ℝ :=
  ((4 : ℝ) / 10 - (55 : ℝ) / 100 * Real.sin theta) / Real.sin theta

/-- The corresponding primitive coordinate point. -/
noncomputable def q0q1RayRayPoint : PrimitiveGeometry.R2 :=
  karlssonOEISQ1.anchor + q0q1RayRayTime • karlssonOEISQ1.rayDirection

private theorem theta_pos : 0 < theta := by
  norm_num [theta]

private theorem theta_lt_pi : theta < Real.pi := by
  have htheta : theta < (3 : ℝ) := by
    norm_num [theta]
  exact htheta.trans Real.pi_gt_three

private theorem sin_theta_pos : 0 < Real.sin theta :=
  Real.sin_pos_of_pos_of_lt_pi theta_pos theta_lt_pi

private theorem sin_theta_lt_small : Real.sin theta < theta :=
  Real.sin_lt theta_pos

theorem q0q1RayRayTime_pos : 0 < q0q1RayRayTime := by
  unfold q0q1RayRayTime
  have hnum : 0 < (4 : ℝ) / 10 - (55 : ℝ) / 100 * Real.sin theta := by
    have hsmall : Real.sin theta < (1 : ℝ) / 100 := by
      simpa [theta] using sin_theta_lt_small
    nlinarith [hsmall]
  exact div_pos hnum sin_theta_pos

private theorem cos_theta_gt_half : (1 / 2 : ℝ) < Real.cos theta := by
  have hcos :=
    Real.one_sub_sq_div_two_lt_cos
      (x := theta) (by norm_num [theta])
  have hhalf : (1 / 2 : ℝ) < 1 - theta ^ 2 / 2 := by
    norm_num [theta]
  exact hhalf.trans hcos

theorem q0q1RayRayTime_gt_one : 1 < q0q1RayRayTime := by
  unfold q0q1RayRayTime
  rw [lt_div_iff₀ sin_theta_pos]
  have hsmall : Real.sin theta < (1 : ℝ) / 100 := by
    simpa [theta] using sin_theta_lt_small
  nlinarith

theorem q0q1RayRayPoint_y_eq_zero :
    q0q1RayRayPoint 1 = 0 := by
  have hsin_ne : Real.sin ((1 : ℝ) / 100) ≠ 0 := by
    simpa [theta] using sin_theta_pos.ne'
  unfold q0q1RayRayPoint q0q1RayRayTime
  simp [ExplicitInputs.karlssonOEISQ1, EuclideanLollipop.fromCenter,
    angleDirection, point2, Real.sin_neg, theta]
  field_simp [hsin_ne]
  ring

theorem q0q1RayRayPoint_x_nonneg :
    0 ≤ q0q1RayRayPoint 0 := by
  have htime_nonneg : 0 ≤ q0q1RayRayTime := q0q1RayRayTime_pos.le
  have hcos_pos : 0 < Real.cos theta := by
    apply Real.cos_pos_of_mem_Ioo
    constructor <;> nlinarith [Real.pi_gt_three]
  have hcos_pos' : 0 < Real.cos ((1 : ℝ) / 100) := by
    simpa [theta] using hcos_pos
  unfold q0q1RayRayPoint
  simp [ExplicitInputs.karlssonOEISQ1, EuclideanLollipop.fromCenter,
    angleDirection, point2, Real.cos_neg]
  nlinarith [mul_nonneg htime_nonneg hcos_pos'.le]

theorem q0q1RayRayPoint_x_gt_one :
    1 < q0q1RayRayPoint 0 := by
  have hcos_half :
      (1 / 2 : ℝ) < Real.cos ((1 : ℝ) / 100) := by
    simpa [theta] using cos_theta_gt_half
  have hcos_pos :
      0 < Real.cos ((1 : ℝ) / 100) := by
    nlinarith
  have hmul :
      Real.cos ((1 : ℝ) / 100) <
        q0q1RayRayTime * Real.cos ((1 : ℝ) / 100) := by
    simpa [one_mul] using
      (mul_lt_mul_of_pos_right q0q1RayRayTime_gt_one hcos_pos)
  have htime_cos :
      (1 / 2 : ℝ) <
        q0q1RayRayTime * Real.cos ((1 : ℝ) / 100) :=
    hcos_half.trans hmul
  unfold q0q1RayRayPoint
  simp [ExplicitInputs.karlssonOEISQ1, EuclideanLollipop.fromCenter,
    angleDirection, point2, Real.cos_neg]
  nlinarith

/-- The explicit point lies on the `Q1` ray by construction. -/
theorem q0q1RayRayPoint_mem_q1_ray :
    q0q1RayRayPoint ∈
      raySet ExplicitInputs.karlssonOEISQ1.anchor
        ExplicitInputs.karlssonOEISQ1.rayDirection := by
  exact ⟨q0q1RayRayTime, q0q1RayRayTime_pos.le, rfl⟩

/-- The same point lies on the `Q0` ray because its y-coordinate is zero and
its x-coordinate is nonnegative. -/
theorem q0q1RayRayPoint_mem_q0_ray :
    q0q1RayRayPoint ∈
      raySet ExplicitInputs.karlssonOEISQ0.anchor
        ExplicitInputs.karlssonOEISQ0.rayDirection := by
  refine ⟨q0q1RayRayPoint 0, q0q1RayRayPoint_x_nonneg, ?_⟩
  ext i
  fin_cases i
  · simp [ExplicitInputs.karlssonOEISQ0, EuclideanLollipop.fromAnchor,
      angleDirection, point2]
  · simp [ExplicitInputs.karlssonOEISQ0, EuclideanLollipop.fromAnchor,
      angleDirection, point2, q0q1RayRayPoint_y_eq_zero]

/-- Primitive carrier-intersection form of the explicit `Q0,Q1` ray-ray
intersection point. -/
theorem q0q1RayRayPoint_mem_pairIntersectionSet :
    q0q1RayRayPoint ∈
      pairIntersectionSet ExplicitInputs.karlssonOEISQ0
        ExplicitInputs.karlssonOEISQ1 := by
  exact ⟨Or.inr q0q1RayRayPoint_mem_q0_ray,
    Or.inr q0q1RayRayPoint_mem_q1_ray⟩

/-- Arrangement-indexed carrier-intersection form. -/
theorem q0q1RayRayPoint_mem_base_pairIntersectionSet :
    q0q1RayRayPoint ∈
      ExplicitInputs.karlssonOEISBaseArrangement.pairIntersectionSet
        (0 : Fin 4) (1 : Fin 4) := by
  simpa [EuclideanLollipopArrangement.pairIntersectionSet] using
    q0q1RayRayPoint_mem_pairIntersectionSet

/-- Lifted ray-ray component form. -/
theorem q0q1RayRayPoint_mem_euclideanRayRaySet :
    toEuclideanR2 q0q1RayRayPoint ∈
      euclideanRayRaySet ExplicitInputs.karlssonOEISQ0
        ExplicitInputs.karlssonOEISQ1 := by
  constructor
  · exact
      (mem_raySet_iff_mem_euclideanRaySet
        (p := q0q1RayRayPoint)
        (anchor := ExplicitInputs.karlssonOEISQ0.anchor)
        (direction := ExplicitInputs.karlssonOEISQ0.rayDirection)).1
        q0q1RayRayPoint_mem_q0_ray
  · exact
      (mem_raySet_iff_mem_euclideanRaySet
        (p := q0q1RayRayPoint)
        (anchor := ExplicitInputs.karlssonOEISQ1.anchor)
        (direction := ExplicitInputs.karlssonOEISQ1.rayDirection)).1
        q0q1RayRayPoint_mem_q1_ray

/-- The `Q0,Q1` ray-ray component is nonempty. -/
theorem q0q1RayRaySet_nonempty :
    (euclideanRayRaySet ExplicitInputs.karlssonOEISQ0
      ExplicitInputs.karlssonOEISQ1).Nonempty :=
  ⟨toEuclideanR2 q0q1RayRayPoint, q0q1RayRayPoint_mem_euclideanRayRaySet⟩

/-- Left x-axis intersection of the `Q0` ray with the `Q1` circle. -/
noncomputable def q0q1RayCircleLeftPoint : PrimitiveGeometry.R2 :=
  point2 (((9 : ℝ) - Real.sqrt (57 : ℝ)) / 20) 0

/-- Right x-axis intersection of the `Q0` ray with the `Q1` circle. -/
noncomputable def q0q1RayCircleRightPoint : PrimitiveGeometry.R2 :=
  point2 (((9 : ℝ) + Real.sqrt (57 : ℝ)) / 20) 0

private theorem sqrt_fiftySeven_lt_nine :
    Real.sqrt (57 : ℝ) < 9 := by
  rw [Real.sqrt_lt' (by norm_num : (0 : ℝ) < 9)]
  norm_num

private theorem sqrt_fiftySeven_pos :
    0 < Real.sqrt (57 : ℝ) :=
  Real.sqrt_pos.2 (by norm_num)

theorem q0q1RayCircleLeftPoint_x_nonneg :
    0 ≤ q0q1RayCircleLeftPoint 0 := by
  unfold q0q1RayCircleLeftPoint
  simp [point2]
  nlinarith [sqrt_fiftySeven_lt_nine]

theorem q0q1RayCircleRightPoint_x_nonneg :
    0 ≤ q0q1RayCircleRightPoint 0 := by
  unfold q0q1RayCircleRightPoint
  simp [point2]
  nlinarith [sqrt_fiftySeven_pos]

theorem q0q1RayCircleLeftPoint_x_lt_one :
    q0q1RayCircleLeftPoint 0 < 1 := by
  unfold q0q1RayCircleLeftPoint
  simp [point2]
  nlinarith [sqrt_fiftySeven_pos]

theorem q0q1RayCircleRightPoint_x_lt_one :
    q0q1RayCircleRightPoint 0 < 1 := by
  unfold q0q1RayCircleRightPoint
  simp [point2]
  nlinarith [sqrt_fiftySeven_lt_nine]

theorem q0q1RayCircleLeftPoint_mem_q0_ray :
    q0q1RayCircleLeftPoint ∈
      raySet ExplicitInputs.karlssonOEISQ0.anchor
        ExplicitInputs.karlssonOEISQ0.rayDirection := by
  refine ⟨q0q1RayCircleLeftPoint 0, q0q1RayCircleLeftPoint_x_nonneg, ?_⟩
  ext i
  fin_cases i <;>
    simp [q0q1RayCircleLeftPoint, ExplicitInputs.karlssonOEISQ0,
      EuclideanLollipop.fromAnchor, angleDirection, point2]

theorem q0q1RayCircleRightPoint_mem_q0_ray :
    q0q1RayCircleRightPoint ∈
      raySet ExplicitInputs.karlssonOEISQ0.anchor
        ExplicitInputs.karlssonOEISQ0.rayDirection := by
  refine ⟨q0q1RayCircleRightPoint 0, q0q1RayCircleRightPoint_x_nonneg, ?_⟩
  ext i
  fin_cases i <;>
    simp [q0q1RayCircleRightPoint, ExplicitInputs.karlssonOEISQ0,
      EuclideanLollipop.fromAnchor, angleDirection, point2]

theorem q0q1RayCircleLeftPoint_mem_q1_circle :
    q0q1RayCircleLeftPoint ∈
      circleSet ExplicitInputs.karlssonOEISQ1.center
        ExplicitInputs.karlssonOEISQ1.radius := by
  unfold q0q1RayCircleLeftPoint circleSet
    TheoremOneEndToEnd.PaulsenLinearAlgebra.distSq2
    TheoremOneEndToEnd.PaulsenLinearAlgebra.normSq2
    TheoremOneEndToEnd.PaulsenLinearAlgebra.dot2
  simp [ExplicitInputs.karlssonOEISQ1, EuclideanLollipop.fromCenter,
    point2]
  ring_nf
  rw [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 57)]
  norm_num

theorem q0q1RayCircleRightPoint_mem_q1_circle :
    q0q1RayCircleRightPoint ∈
      circleSet ExplicitInputs.karlssonOEISQ1.center
        ExplicitInputs.karlssonOEISQ1.radius := by
  unfold q0q1RayCircleRightPoint circleSet
    TheoremOneEndToEnd.PaulsenLinearAlgebra.distSq2
    TheoremOneEndToEnd.PaulsenLinearAlgebra.normSq2
    TheoremOneEndToEnd.PaulsenLinearAlgebra.dot2
  simp [ExplicitInputs.karlssonOEISQ1, EuclideanLollipop.fromCenter,
    point2]
  ring_nf
  rw [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 57)]
  norm_num

/-- Primitive classification of the mixed component
`ray(Q0) ∩ circle(Q1)`: every point in it is one of the two explicit x-axis
circle hits. -/
theorem q0q1RayCircle_eq_left_or_right_of_mem
    {p : PrimitiveGeometry.R2}
    (hray :
      p ∈ raySet ExplicitInputs.karlssonOEISQ0.anchor
        ExplicitInputs.karlssonOEISQ0.rayDirection)
    (hcircle :
      p ∈ circleSet ExplicitInputs.karlssonOEISQ1.center
        ExplicitInputs.karlssonOEISQ1.radius) :
    p = q0q1RayCircleLeftPoint ∨
      p = q0q1RayCircleRightPoint := by
  rcases hray with ⟨t, _ht, hp⟩
  subst p
  have hc := hcircle
  unfold circleSet
    TheoremOneEndToEnd.PaulsenLinearAlgebra.distSq2
    TheoremOneEndToEnd.PaulsenLinearAlgebra.normSq2
    TheoremOneEndToEnd.PaulsenLinearAlgebra.dot2 at hc
  simp [ExplicitInputs.karlssonOEISQ0, ExplicitInputs.karlssonOEISQ1,
    EuclideanLollipop.fromAnchor, EuclideanLollipop.fromCenter,
    angleDirection, point2] at hc
  have hroot_sq :
      (Real.sqrt (57 : ℝ) / 20) ^ 2 = (57 : ℝ) / 400 := by
    rw [div_pow, Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 57)]
    norm_num
  have hsq :
      (t - (9 : ℝ) / 20) ^ 2 =
        (Real.sqrt (57 : ℝ) / 20) ^ 2 := by
    rw [hroot_sq]
    nlinarith [hc]
  rcases (sq_eq_sq_iff_eq_or_eq_neg.mp hsq) with hpos | hneg
  · right
    have ht :
        t = ((9 : ℝ) + Real.sqrt (57 : ℝ)) / 20 := by
      linarith
    ext i
    fin_cases i <;>
      simp [ExplicitInputs.karlssonOEISQ0, EuclideanLollipop.fromAnchor,
        angleDirection, q0q1RayCircleRightPoint, point2, ht]
  · left
    have ht :
        t = ((9 : ℝ) - Real.sqrt (57 : ℝ)) / 20 := by
      linarith
    ext i
    fin_cases i <;>
      simp [ExplicitInputs.karlssonOEISQ0, EuclideanLollipop.fromAnchor,
        angleDirection, q0q1RayCircleLeftPoint, point2, ht]

/-- Lifted Euclidean-space form of the `ray(Q0) ∩ circle(Q1)` classification. -/
theorem q0q1EuclideanRayCircle_eq_left_or_right_of_mem
    {p : EuclideanR2}
    (hp :
      p ∈ euclideanRayCircleSet ExplicitInputs.karlssonOEISQ0
        ExplicitInputs.karlssonOEISQ1) :
    p = toEuclideanR2 q0q1RayCircleLeftPoint ∨
      p = toEuclideanR2 q0q1RayCircleRightPoint := by
  rcases hp.1 with ⟨t, ht, hp_eq⟩
  let x : PrimitiveGeometry.R2 :=
    ExplicitInputs.karlssonOEISQ0.anchor +
      t • ExplicitInputs.karlssonOEISQ0.rayDirection
  have hp_to : p = toEuclideanR2 x := by
    dsimp [x]
    simpa using hp_eq
  have hx_ray :
      x ∈ raySet ExplicitInputs.karlssonOEISQ0.anchor
        ExplicitInputs.karlssonOEISQ0.rayDirection := by
    exact ⟨t, ht, rfl⟩
  have hx_circle :
      x ∈ circleSet ExplicitInputs.karlssonOEISQ1.center
        ExplicitInputs.karlssonOEISQ1.radius := by
    have hx_sphere :
        toEuclideanR2 x ∈
          euclideanSphere ExplicitInputs.karlssonOEISQ1.center
            ExplicitInputs.karlssonOEISQ1.radius := by
      rw [← hp_to]
      exact hp.2
    exact
      (mem_circleSet_iff_mem_euclideanSphere
        ExplicitInputs.karlssonOEISQ1.radius_pos.le).2
        hx_sphere
  rcases q0q1RayCircle_eq_left_or_right_of_mem hx_ray hx_circle with
    hleft | hright
  · left
    simpa [hleft] using hp_to
  · right
    simpa [hright] using hp_to

/-- Primitive radical-axis relation for the two exact OEIS circles
`circle(Q0)` and `circle(Q1)`. -/
theorem q0q1CircleCircle_linear_relation_of_mem
    {p : PrimitiveGeometry.R2}
    (h0 :
      p ∈ circleSet ExplicitInputs.karlssonOEISQ0.center
        ExplicitInputs.karlssonOEISQ0.radius)
    (h1 :
      p ∈ circleSet ExplicitInputs.karlssonOEISQ1.center
        ExplicitInputs.karlssonOEISQ1.radius) :
    (20045 : ℝ) * p 0 + 40 * p 1 = 3 := by
  have h0' := h0
  unfold circleSet
    TheoremOneEndToEnd.PaulsenLinearAlgebra.distSq2
    TheoremOneEndToEnd.PaulsenLinearAlgebra.normSq2
    TheoremOneEndToEnd.PaulsenLinearAlgebra.dot2 at h0'
  simp [ExplicitInputs.karlssonOEISQ0, EuclideanLollipop.fromAnchor,
    angleDirection, point2] at h0'
  have h1' := h1
  unfold circleSet
    TheoremOneEndToEnd.PaulsenLinearAlgebra.distSq2
    TheoremOneEndToEnd.PaulsenLinearAlgebra.normSq2
    TheoremOneEndToEnd.PaulsenLinearAlgebra.dot2 at h1'
  simp [ExplicitInputs.karlssonOEISQ1, EuclideanLollipop.fromCenter,
    point2] at h1'
  nlinarith

/-- Lifted Euclidean-space form of the exact radical-axis relation for
`circle(Q0) ∩ circle(Q1)`. -/
theorem q0q1EuclideanCircleCircle_linear_relation_of_mem
    {p : EuclideanR2}
    (hp :
      p ∈ euclideanCircleCircleSet ExplicitInputs.karlssonOEISQ0
        ExplicitInputs.karlssonOEISQ1) :
    (20045 : ℝ) * p 0 + 40 * p 1 = 3 := by
  let x : PrimitiveGeometry.R2 := fun i => p i
  have hx_to : toEuclideanR2 x = p := by
    ext i
    rfl
  have hx0 :
      x ∈ circleSet ExplicitInputs.karlssonOEISQ0.center
        ExplicitInputs.karlssonOEISQ0.radius := by
    have hx0_sphere :
        toEuclideanR2 x ∈
          euclideanSphere ExplicitInputs.karlssonOEISQ0.center
            ExplicitInputs.karlssonOEISQ0.radius := by
      rw [hx_to]
      exact hp.1
    exact
      (mem_circleSet_iff_mem_euclideanSphere
        ExplicitInputs.karlssonOEISQ0.radius_pos.le).2
        hx0_sphere
  have hx1 :
      x ∈ circleSet ExplicitInputs.karlssonOEISQ1.center
        ExplicitInputs.karlssonOEISQ1.radius := by
    have hx1_sphere :
        toEuclideanR2 x ∈
          euclideanSphere ExplicitInputs.karlssonOEISQ1.center
            ExplicitInputs.karlssonOEISQ1.radius := by
      rw [hx_to]
      exact hp.2
    exact
      (mem_circleSet_iff_mem_euclideanSphere
        ExplicitInputs.karlssonOEISQ1.radius_pos.le).2
        hx1_sphere
  simpa [x] using q0q1CircleCircle_linear_relation_of_mem hx0 hx1

/-- Upper exact intersection point of `circle(Q0)` and `circle(Q1)`. -/
noncomputable def q0q1CircleCircleUpperPoint : PrimitiveGeometry.R2 :=
  let x : ℝ :=
    ((-51973 : ℝ) - 8 * Real.sqrt (39945991 : ℝ)) / 80360725
  point2 x ((3 - 20045 * x) / 40)

/-- Lower exact intersection point of `circle(Q0)` and `circle(Q1)`. -/
noncomputable def q0q1CircleCircleLowerPoint : PrimitiveGeometry.R2 :=
  let x : ℝ :=
    ((-51973 : ℝ) + 8 * Real.sqrt (39945991 : ℝ)) / 80360725
  point2 x ((3 - 20045 * x) / 40)

theorem q0q1CircleCircleUpperPoint_mem_q0_circle :
    q0q1CircleCircleUpperPoint ∈
      circleSet ExplicitInputs.karlssonOEISQ0.center
        ExplicitInputs.karlssonOEISQ0.radius := by
  unfold q0q1CircleCircleUpperPoint circleSet
    TheoremOneEndToEnd.PaulsenLinearAlgebra.distSq2
    TheoremOneEndToEnd.PaulsenLinearAlgebra.normSq2
    TheoremOneEndToEnd.PaulsenLinearAlgebra.dot2
  simp [ExplicitInputs.karlssonOEISQ0, EuclideanLollipop.fromAnchor,
    angleDirection, point2]
  ring_nf
  rw [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 39945991)]
  norm_num

theorem q0q1CircleCircleLowerPoint_mem_q0_circle :
    q0q1CircleCircleLowerPoint ∈
      circleSet ExplicitInputs.karlssonOEISQ0.center
        ExplicitInputs.karlssonOEISQ0.radius := by
  unfold q0q1CircleCircleLowerPoint circleSet
    TheoremOneEndToEnd.PaulsenLinearAlgebra.distSq2
    TheoremOneEndToEnd.PaulsenLinearAlgebra.normSq2
    TheoremOneEndToEnd.PaulsenLinearAlgebra.dot2
  simp [ExplicitInputs.karlssonOEISQ0, EuclideanLollipop.fromAnchor,
    angleDirection, point2]
  ring_nf
  rw [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 39945991)]
  norm_num

theorem q0q1CircleCircleUpperPoint_mem_q1_circle :
    q0q1CircleCircleUpperPoint ∈
      circleSet ExplicitInputs.karlssonOEISQ1.center
        ExplicitInputs.karlssonOEISQ1.radius := by
  unfold q0q1CircleCircleUpperPoint circleSet
    TheoremOneEndToEnd.PaulsenLinearAlgebra.distSq2
    TheoremOneEndToEnd.PaulsenLinearAlgebra.normSq2
    TheoremOneEndToEnd.PaulsenLinearAlgebra.dot2
  simp [ExplicitInputs.karlssonOEISQ1, EuclideanLollipop.fromCenter,
    point2]
  ring_nf
  rw [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 39945991)]
  norm_num

theorem q0q1CircleCircleLowerPoint_mem_q1_circle :
    q0q1CircleCircleLowerPoint ∈
      circleSet ExplicitInputs.karlssonOEISQ1.center
        ExplicitInputs.karlssonOEISQ1.radius := by
  unfold q0q1CircleCircleLowerPoint circleSet
    TheoremOneEndToEnd.PaulsenLinearAlgebra.distSq2
    TheoremOneEndToEnd.PaulsenLinearAlgebra.normSq2
    TheoremOneEndToEnd.PaulsenLinearAlgebra.dot2
  simp [ExplicitInputs.karlssonOEISQ1, EuclideanLollipop.fromCenter,
    point2]
  ring_nf
  rw [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 39945991)]
  norm_num

private theorem sqrt_circleCircle_pos :
    0 < Real.sqrt (39945991 : ℝ) :=
  Real.sqrt_pos.2 (by norm_num)

private theorem sqrt_circleCircle_lt_eight_thousand :
    Real.sqrt (39945991 : ℝ) < 8000 := by
  rw [Real.sqrt_lt' (by norm_num : (0 : ℝ) < 8000)]
  norm_num

theorem q0q1CircleCircleUpperPoint_y_pos :
    0 < q0q1CircleCircleUpperPoint 1 := by
  unfold q0q1CircleCircleUpperPoint
  simp [point2]
  nlinarith [sqrt_circleCircle_pos]

theorem q0q1CircleCircleLowerPoint_y_pos :
    0 < q0q1CircleCircleLowerPoint 1 := by
  unfold q0q1CircleCircleLowerPoint
  simp [point2]
  nlinarith [sqrt_circleCircle_lt_eight_thousand]

theorem q0q1CircleCircleUpperPoint_ne_lower :
    q0q1CircleCircleUpperPoint ≠ q0q1CircleCircleLowerPoint := by
  intro h
  have hx := congr_fun h 0
  simp [q0q1CircleCircleUpperPoint, q0q1CircleCircleLowerPoint] at hx
  nlinarith [sqrt_circleCircle_pos]

theorem q0q1CircleCircleUpperPoint_mem_euclideanCircleCircleSet :
    toEuclideanR2 q0q1CircleCircleUpperPoint ∈
      euclideanCircleCircleSet ExplicitInputs.karlssonOEISQ0
        ExplicitInputs.karlssonOEISQ1 := by
  constructor
  · exact
      (mem_circleSet_iff_mem_euclideanSphere
        ExplicitInputs.karlssonOEISQ0.radius_pos.le).1
        q0q1CircleCircleUpperPoint_mem_q0_circle
  · exact
      (mem_circleSet_iff_mem_euclideanSphere
        ExplicitInputs.karlssonOEISQ1.radius_pos.le).1
        q0q1CircleCircleUpperPoint_mem_q1_circle

theorem q0q1CircleCircleLowerPoint_mem_euclideanCircleCircleSet :
    toEuclideanR2 q0q1CircleCircleLowerPoint ∈
      euclideanCircleCircleSet ExplicitInputs.karlssonOEISQ0
        ExplicitInputs.karlssonOEISQ1 := by
  constructor
  · exact
      (mem_circleSet_iff_mem_euclideanSphere
        ExplicitInputs.karlssonOEISQ0.radius_pos.le).1
        q0q1CircleCircleLowerPoint_mem_q0_circle
  · exact
      (mem_circleSet_iff_mem_euclideanSphere
        ExplicitInputs.karlssonOEISQ1.radius_pos.le).1
        q0q1CircleCircleLowerPoint_mem_q1_circle

/-- Primitive classification of the circle-circle component
`circle(Q0) ∩ circle(Q1)`: every point in it is one of the two explicit
radical-coordinate points. -/
theorem q0q1CircleCircle_eq_upper_or_lower_of_mem
    {p : PrimitiveGeometry.R2}
    (h0 :
      p ∈ circleSet ExplicitInputs.karlssonOEISQ0.center
        ExplicitInputs.karlssonOEISQ0.radius)
    (h1 :
      p ∈ circleSet ExplicitInputs.karlssonOEISQ1.center
        ExplicitInputs.karlssonOEISQ1.radius) :
    p = q0q1CircleCircleUpperPoint ∨
      p = q0q1CircleCircleLowerPoint := by
  exact
    eq_or_eq_of_mem_circleSet_inter_of_two_witnesses
      (L := ExplicitInputs.karlssonOEISQ0)
      (M := ExplicitInputs.karlssonOEISQ1)
      ExplicitInputs.karlssonOEISQ0_Q1_spheres_distinct
      q0q1CircleCircleUpperPoint_ne_lower
      ⟨q0q1CircleCircleUpperPoint_mem_q0_circle,
        q0q1CircleCircleUpperPoint_mem_q1_circle⟩
      ⟨q0q1CircleCircleLowerPoint_mem_q0_circle,
        q0q1CircleCircleLowerPoint_mem_q1_circle⟩
      ⟨h0, h1⟩

/-- Lifted Euclidean-space form of the exact `circle(Q0) ∩ circle(Q1)`
classification. -/
theorem q0q1EuclideanCircleCircle_eq_upper_or_lower_of_mem
    {p : EuclideanR2}
    (hp :
      p ∈ euclideanCircleCircleSet ExplicitInputs.karlssonOEISQ0
        ExplicitInputs.karlssonOEISQ1) :
    p = toEuclideanR2 q0q1CircleCircleUpperPoint ∨
      p = toEuclideanR2 q0q1CircleCircleLowerPoint := by
  let x : PrimitiveGeometry.R2 := fun i => p i
  have hx_to : toEuclideanR2 x = p := by
    ext i
    rfl
  have hx0 :
      x ∈ circleSet ExplicitInputs.karlssonOEISQ0.center
        ExplicitInputs.karlssonOEISQ0.radius := by
    have hx0_sphere :
        toEuclideanR2 x ∈
          euclideanSphere ExplicitInputs.karlssonOEISQ0.center
            ExplicitInputs.karlssonOEISQ0.radius := by
      rw [hx_to]
      exact hp.1
    exact
      (mem_circleSet_iff_mem_euclideanSphere
        ExplicitInputs.karlssonOEISQ0.radius_pos.le).2
        hx0_sphere
  have hx1 :
      x ∈ circleSet ExplicitInputs.karlssonOEISQ1.center
        ExplicitInputs.karlssonOEISQ1.radius := by
    have hx1_sphere :
        toEuclideanR2 x ∈
          euclideanSphere ExplicitInputs.karlssonOEISQ1.center
            ExplicitInputs.karlssonOEISQ1.radius := by
      rw [hx_to]
      exact hp.2
    exact
      (mem_circleSet_iff_mem_euclideanSphere
        ExplicitInputs.karlssonOEISQ1.radius_pos.le).2
        hx1_sphere
  rcases q0q1CircleCircle_eq_upper_or_lower_of_mem hx0 hx1 with
    hupper | hlower
  · left
    simpa [hupper] using hx_to.symm
  · right
    simpa [hlower] using hx_to.symm

theorem q0q1RayCircleLeftPoint_mem_pairIntersectionSet :
    q0q1RayCircleLeftPoint ∈
      pairIntersectionSet ExplicitInputs.karlssonOEISQ0
        ExplicitInputs.karlssonOEISQ1 := by
  exact ⟨Or.inr q0q1RayCircleLeftPoint_mem_q0_ray,
    Or.inl q0q1RayCircleLeftPoint_mem_q1_circle⟩

theorem q0q1RayCircleRightPoint_mem_pairIntersectionSet :
    q0q1RayCircleRightPoint ∈
      pairIntersectionSet ExplicitInputs.karlssonOEISQ0
        ExplicitInputs.karlssonOEISQ1 := by
  exact ⟨Or.inr q0q1RayCircleRightPoint_mem_q0_ray,
    Or.inl q0q1RayCircleRightPoint_mem_q1_circle⟩

theorem q0q1CircleCircleUpperPoint_mem_pairIntersectionSet :
    q0q1CircleCircleUpperPoint ∈
      pairIntersectionSet ExplicitInputs.karlssonOEISQ0
        ExplicitInputs.karlssonOEISQ1 := by
  exact ⟨Or.inl q0q1CircleCircleUpperPoint_mem_q0_circle,
    Or.inl q0q1CircleCircleUpperPoint_mem_q1_circle⟩

theorem q0q1CircleCircleLowerPoint_mem_pairIntersectionSet :
    q0q1CircleCircleLowerPoint ∈
      pairIntersectionSet ExplicitInputs.karlssonOEISQ0
        ExplicitInputs.karlssonOEISQ1 := by
  exact ⟨Or.inl q0q1CircleCircleLowerPoint_mem_q0_circle,
    Or.inl q0q1CircleCircleLowerPoint_mem_q1_circle⟩

theorem q0q1RayCircleLeftPoint_mem_base_pairIntersectionSet :
    q0q1RayCircleLeftPoint ∈
      ExplicitInputs.karlssonOEISBaseArrangement.pairIntersectionSet
        (0 : Fin 4) (1 : Fin 4) := by
  simpa [EuclideanLollipopArrangement.pairIntersectionSet] using
    q0q1RayCircleLeftPoint_mem_pairIntersectionSet

theorem q0q1RayCircleRightPoint_mem_base_pairIntersectionSet :
    q0q1RayCircleRightPoint ∈
      ExplicitInputs.karlssonOEISBaseArrangement.pairIntersectionSet
        (0 : Fin 4) (1 : Fin 4) := by
  simpa [EuclideanLollipopArrangement.pairIntersectionSet] using
    q0q1RayCircleRightPoint_mem_pairIntersectionSet

theorem q0q1CircleCircleUpperPoint_mem_base_pairIntersectionSet :
    q0q1CircleCircleUpperPoint ∈
      ExplicitInputs.karlssonOEISBaseArrangement.pairIntersectionSet
        (0 : Fin 4) (1 : Fin 4) := by
  simpa [EuclideanLollipopArrangement.pairIntersectionSet] using
    q0q1CircleCircleUpperPoint_mem_pairIntersectionSet

theorem q0q1CircleCircleLowerPoint_mem_base_pairIntersectionSet :
    q0q1CircleCircleLowerPoint ∈
      ExplicitInputs.karlssonOEISBaseArrangement.pairIntersectionSet
        (0 : Fin 4) (1 : Fin 4) := by
  simpa [EuclideanLollipopArrangement.pairIntersectionSet] using
    q0q1CircleCircleLowerPoint_mem_pairIntersectionSet

theorem q0q1RayCircleLeftPoint_mem_euclideanRayCircleSet :
    toEuclideanR2 q0q1RayCircleLeftPoint ∈
      euclideanRayCircleSet ExplicitInputs.karlssonOEISQ0
        ExplicitInputs.karlssonOEISQ1 := by
  constructor
  · exact
      (mem_raySet_iff_mem_euclideanRaySet
        (p := q0q1RayCircleLeftPoint)
        (anchor := ExplicitInputs.karlssonOEISQ0.anchor)
        (direction := ExplicitInputs.karlssonOEISQ0.rayDirection)).1
        q0q1RayCircleLeftPoint_mem_q0_ray
  · exact
      (mem_circleSet_iff_mem_euclideanSphere
        ExplicitInputs.karlssonOEISQ1.radius_pos.le).1
        q0q1RayCircleLeftPoint_mem_q1_circle

theorem q0q1RayCircleRightPoint_mem_euclideanRayCircleSet :
    toEuclideanR2 q0q1RayCircleRightPoint ∈
      euclideanRayCircleSet ExplicitInputs.karlssonOEISQ0
        ExplicitInputs.karlssonOEISQ1 := by
  constructor
  · exact
      (mem_raySet_iff_mem_euclideanRaySet
        (p := q0q1RayCircleRightPoint)
        (anchor := ExplicitInputs.karlssonOEISQ0.anchor)
        (direction := ExplicitInputs.karlssonOEISQ0.rayDirection)).1
        q0q1RayCircleRightPoint_mem_q0_ray
  · exact
      (mem_circleSet_iff_mem_euclideanSphere
        ExplicitInputs.karlssonOEISQ1.radius_pos.le).1
        q0q1RayCircleRightPoint_mem_q1_circle

theorem q0q1RayCircleLeftPoint_ne_right :
    q0q1RayCircleLeftPoint ≠ q0q1RayCircleRightPoint := by
  intro h
  have hx := congr_fun h 0
  simp [q0q1RayCircleLeftPoint, q0q1RayCircleRightPoint, point2] at hx
  nlinarith [sqrt_fiftySeven_pos]

/-- Any exact six-pair finite crossing certificate for the OEIS/Karlsson base
must include at least one point in its `(Q0,Q1)` finite witness. -/
theorem pair01_crossingPoints_nonempty
    (C : ExplicitInputs.KarlssonOEISBaseSixPairCoordinateCrossingCertificate) :
    C.pair01.crossingPoints.Nonempty := by
  have hp_set :
      q0q1RayRayPoint ∈
      ((C.pair01.crossingPoints : Finset R2) : Set R2) := by
    rw [C.pair01.crossingPoints_spec]
    exact q0q1RayRayPoint_mem_base_pairIntersectionSet
  exact ⟨q0q1RayRayPoint, by simpa using hp_set⟩

/-- Cardinality consequence of the explicit ray-ray point. -/
theorem pair01_crossingPoints_card_pos
    (C : ExplicitInputs.KarlssonOEISBaseSixPairCoordinateCrossingCertificate) :
    0 < C.pair01.crossingPoints.card :=
  Finset.card_pos.2 (pair01_crossingPoints_nonempty C)

theorem pair01_crossingPoints_mem_rayRay
    (C : ExplicitInputs.KarlssonOEISBaseSixPairCoordinateCrossingCertificate) :
    q0q1RayRayPoint ∈ C.pair01.crossingPoints := by
  have hp_set :
      q0q1RayRayPoint ∈
        ((C.pair01.crossingPoints : Finset PrimitiveGeometry.R2) :
          Set PrimitiveGeometry.R2) := by
    rw [C.pair01.crossingPoints_spec]
    exact q0q1RayRayPoint_mem_base_pairIntersectionSet
  simpa using hp_set

theorem pair01_crossingPoints_mem_rayCircleLeft
    (C : ExplicitInputs.KarlssonOEISBaseSixPairCoordinateCrossingCertificate) :
    q0q1RayCircleLeftPoint ∈ C.pair01.crossingPoints := by
  have hp_set :
      q0q1RayCircleLeftPoint ∈
        ((C.pair01.crossingPoints : Finset PrimitiveGeometry.R2) :
          Set PrimitiveGeometry.R2) := by
    rw [C.pair01.crossingPoints_spec]
    exact q0q1RayCircleLeftPoint_mem_base_pairIntersectionSet
  simpa using hp_set

theorem pair01_crossingPoints_mem_rayCircleRight
    (C : ExplicitInputs.KarlssonOEISBaseSixPairCoordinateCrossingCertificate) :
    q0q1RayCircleRightPoint ∈ C.pair01.crossingPoints := by
  have hp_set :
      q0q1RayCircleRightPoint ∈
        ((C.pair01.crossingPoints : Finset PrimitiveGeometry.R2) :
          Set PrimitiveGeometry.R2) := by
    rw [C.pair01.crossingPoints_spec]
    exact q0q1RayCircleRightPoint_mem_base_pairIntersectionSet
  simpa using hp_set

/-- The exact two x-axis circle hits already force the `(Q0,Q1)` finite
witness to have at least two points. -/
theorem pair01_crossingPoints_two_le_card
    (C : ExplicitInputs.KarlssonOEISBaseSixPairCoordinateCrossingCertificate) :
    2 ≤ C.pair01.crossingPoints.card := by
  classical
  let T : Finset PrimitiveGeometry.R2 :=
    {q0q1RayCircleLeftPoint, q0q1RayCircleRightPoint}
  have hT_subset : T ⊆ C.pair01.crossingPoints := by
    intro p hp
    simp [T] at hp
    rcases hp with rfl | rfl
    · exact pair01_crossingPoints_mem_rayCircleLeft C
    · exact pair01_crossingPoints_mem_rayCircleRight C
  have hT_card : T.card = 2 := by
    simp [T, q0q1RayCircleLeftPoint_ne_right]
  have hcard := Finset.card_le_card hT_subset
  simpa [hT_card] using hcard

theorem pair01_crossingPoints_mem_circleCircleUpper
    (C : ExplicitInputs.KarlssonOEISBaseSixPairCoordinateCrossingCertificate) :
    q0q1CircleCircleUpperPoint ∈ C.pair01.crossingPoints := by
  have hp_set :
      q0q1CircleCircleUpperPoint ∈
        ((C.pair01.crossingPoints : Finset PrimitiveGeometry.R2) :
          Set PrimitiveGeometry.R2) := by
    rw [C.pair01.crossingPoints_spec]
    exact q0q1CircleCircleUpperPoint_mem_base_pairIntersectionSet
  simpa using hp_set

theorem pair01_crossingPoints_mem_circleCircleLower
    (C : ExplicitInputs.KarlssonOEISBaseSixPairCoordinateCrossingCertificate) :
    q0q1CircleCircleLowerPoint ∈ C.pair01.crossingPoints := by
  have hp_set :
      q0q1CircleCircleLowerPoint ∈
        ((C.pair01.crossingPoints : Finset PrimitiveGeometry.R2) :
          Set PrimitiveGeometry.R2) := by
    rw [C.pair01.crossingPoints_spec]
    exact q0q1CircleCircleLowerPoint_mem_base_pairIntersectionSet
  simpa using hp_set

theorem q0q1CircleCircleUpperPoint_ne_rayCircleLeft :
    q0q1CircleCircleUpperPoint ≠ q0q1RayCircleLeftPoint := by
  intro h
  have hpos := q0q1CircleCircleUpperPoint_y_pos
  rw [h] at hpos
  simp [q0q1RayCircleLeftPoint, point2] at hpos

theorem q0q1CircleCircleUpperPoint_ne_rayCircleRight :
    q0q1CircleCircleUpperPoint ≠ q0q1RayCircleRightPoint := by
  intro h
  have hpos := q0q1CircleCircleUpperPoint_y_pos
  rw [h] at hpos
  simp [q0q1RayCircleRightPoint, point2] at hpos

theorem q0q1CircleCircleLowerPoint_ne_rayCircleLeft :
    q0q1CircleCircleLowerPoint ≠ q0q1RayCircleLeftPoint := by
  intro h
  have hpos := q0q1CircleCircleLowerPoint_y_pos
  rw [h] at hpos
  simp [q0q1RayCircleLeftPoint, point2] at hpos

theorem q0q1CircleCircleLowerPoint_ne_rayCircleRight :
    q0q1CircleCircleLowerPoint ≠ q0q1RayCircleRightPoint := by
  intro h
  have hpos := q0q1CircleCircleLowerPoint_y_pos
  rw [h] at hpos
  simp [q0q1RayCircleRightPoint, point2] at hpos

theorem q0q1RayRayPoint_ne_rayCircleLeft :
    q0q1RayRayPoint ≠ q0q1RayCircleLeftPoint := by
  intro h
  have hx_gt := q0q1RayRayPoint_x_gt_one
  rw [h] at hx_gt
  nlinarith [q0q1RayCircleLeftPoint_x_lt_one]

theorem q0q1RayRayPoint_ne_rayCircleRight :
    q0q1RayRayPoint ≠ q0q1RayCircleRightPoint := by
  intro h
  have hx_gt := q0q1RayRayPoint_x_gt_one
  rw [h] at hx_gt
  nlinarith [q0q1RayCircleRightPoint_x_lt_one]

theorem q0q1RayRayPoint_ne_circleCircleUpper :
    q0q1RayRayPoint ≠ q0q1CircleCircleUpperPoint := by
  intro h
  have hpos := q0q1CircleCircleUpperPoint_y_pos
  rw [← h] at hpos
  simp [q0q1RayRayPoint_y_eq_zero] at hpos

theorem q0q1RayRayPoint_ne_circleCircleLower :
    q0q1RayRayPoint ≠ q0q1CircleCircleLowerPoint := by
  intro h
  have hpos := q0q1CircleCircleLowerPoint_y_pos
  rw [← h] at hpos
  simp [q0q1RayRayPoint_y_eq_zero] at hpos

/-- The two x-axis ray-circle points plus the two circle-circle points force
the `(Q0,Q1)` finite witness to have at least four points. -/
theorem pair01_crossingPoints_four_le_card
    (C : ExplicitInputs.KarlssonOEISBaseSixPairCoordinateCrossingCertificate) :
    4 ≤ C.pair01.crossingPoints.card := by
  classical
  let T : Finset PrimitiveGeometry.R2 :=
    {q0q1RayCircleLeftPoint, q0q1RayCircleRightPoint,
      q0q1CircleCircleUpperPoint, q0q1CircleCircleLowerPoint}
  have hT_subset : T ⊆ C.pair01.crossingPoints := by
    intro p hp
    simp [T] at hp
    rcases hp with rfl | rfl | rfl | rfl
    · exact pair01_crossingPoints_mem_rayCircleLeft C
    · exact pair01_crossingPoints_mem_rayCircleRight C
    · exact pair01_crossingPoints_mem_circleCircleUpper C
    · exact pair01_crossingPoints_mem_circleCircleLower C
  have hT_card : T.card = 4 := by
    rw [Finset.card_eq_four]
    refine
      ⟨q0q1RayCircleLeftPoint, q0q1RayCircleRightPoint,
        q0q1CircleCircleUpperPoint, q0q1CircleCircleLowerPoint,
        q0q1RayCircleLeftPoint_ne_right,
        (Ne.symm q0q1CircleCircleUpperPoint_ne_rayCircleLeft),
        (Ne.symm q0q1CircleCircleLowerPoint_ne_rayCircleLeft),
        (Ne.symm q0q1CircleCircleUpperPoint_ne_rayCircleRight),
        (Ne.symm q0q1CircleCircleLowerPoint_ne_rayCircleRight),
        q0q1CircleCircleUpperPoint_ne_lower, ?_⟩
    rfl
  have hcard := Finset.card_le_card hT_subset
  simpa [hT_card] using hcard

/-- The ray-ray point, the two x-axis ray-circle points, and the two
circle-circle points force the `(Q0,Q1)` finite witness to have at least five
points. -/
theorem pair01_crossingPoints_five_le_card
    (C : ExplicitInputs.KarlssonOEISBaseSixPairCoordinateCrossingCertificate) :
    5 ≤ C.pair01.crossingPoints.card := by
  classical
  let U : Finset PrimitiveGeometry.R2 :=
    {q0q1RayCircleLeftPoint, q0q1RayCircleRightPoint,
      q0q1CircleCircleUpperPoint, q0q1CircleCircleLowerPoint}
  let T : Finset PrimitiveGeometry.R2 := insert q0q1RayRayPoint U
  have hU_card : U.card = 4 := by
    rw [Finset.card_eq_four]
    refine
      ⟨q0q1RayCircleLeftPoint, q0q1RayCircleRightPoint,
        q0q1CircleCircleUpperPoint, q0q1CircleCircleLowerPoint,
        q0q1RayCircleLeftPoint_ne_right,
        (Ne.symm q0q1CircleCircleUpperPoint_ne_rayCircleLeft),
        (Ne.symm q0q1CircleCircleLowerPoint_ne_rayCircleLeft),
        (Ne.symm q0q1CircleCircleUpperPoint_ne_rayCircleRight),
        (Ne.symm q0q1CircleCircleLowerPoint_ne_rayCircleRight),
        q0q1CircleCircleUpperPoint_ne_lower, ?_⟩
    rfl
  have hray_not_mem : q0q1RayRayPoint ∉ U := by
    simp [U, q0q1RayRayPoint_ne_rayCircleLeft,
      q0q1RayRayPoint_ne_rayCircleRight,
      q0q1RayRayPoint_ne_circleCircleUpper,
      q0q1RayRayPoint_ne_circleCircleLower]
  have hT_subset : T ⊆ C.pair01.crossingPoints := by
    intro p hp
    simp [T, U] at hp
    rcases hp with rfl | rfl | rfl | rfl | rfl
    · exact pair01_crossingPoints_mem_rayRay C
    · exact pair01_crossingPoints_mem_rayCircleLeft C
    · exact pair01_crossingPoints_mem_rayCircleRight C
    · exact pair01_crossingPoints_mem_circleCircleUpper C
    · exact pair01_crossingPoints_mem_circleCircleLower C
  have hT_card : T.card = 5 := by
    rw [show T.card = (insert q0q1RayRayPoint U).card by rfl]
    rw [Finset.card_insert_of_notMem hray_not_mem]
    omega
  have hcard := Finset.card_le_card hT_subset
  simpa [hT_card] using hcard

/-- The five named points are the exact primitive finite witness for
`(Q0,Q1)`. -/
noncomputable def q0q1FivePointFinset : Finset PrimitiveGeometry.R2 :=
  {q0q1RayRayPoint, q0q1RayCircleLeftPoint, q0q1RayCircleRightPoint,
    q0q1CircleCircleUpperPoint, q0q1CircleCircleLowerPoint}

theorem q0q1FivePointFinset_card :
    q0q1FivePointFinset.card = 5 := by
  classical
  let U : Finset PrimitiveGeometry.R2 :=
    {q0q1RayCircleLeftPoint, q0q1RayCircleRightPoint,
      q0q1CircleCircleUpperPoint, q0q1CircleCircleLowerPoint}
  have hU_card : U.card = 4 := by
    rw [Finset.card_eq_four]
    refine
      ⟨q0q1RayCircleLeftPoint, q0q1RayCircleRightPoint,
        q0q1CircleCircleUpperPoint, q0q1CircleCircleLowerPoint,
        q0q1RayCircleLeftPoint_ne_right,
        (Ne.symm q0q1CircleCircleUpperPoint_ne_rayCircleLeft),
        (Ne.symm q0q1CircleCircleLowerPoint_ne_rayCircleLeft),
        (Ne.symm q0q1CircleCircleUpperPoint_ne_rayCircleRight),
        (Ne.symm q0q1CircleCircleLowerPoint_ne_rayCircleRight),
        q0q1CircleCircleUpperPoint_ne_lower, ?_⟩
    rfl
  have hray_not_mem : q0q1RayRayPoint ∉ U := by
    simp [U, q0q1RayRayPoint_ne_rayCircleLeft,
      q0q1RayRayPoint_ne_rayCircleRight,
      q0q1RayRayPoint_ne_circleCircleUpper,
      q0q1RayRayPoint_ne_circleCircleLower]
  change (insert q0q1RayRayPoint U).card = 5
  rw [Finset.card_insert_of_notMem hray_not_mem]
  omega

theorem q0q1CircleRay_false_of_mem
    {p : PrimitiveGeometry.R2}
    (hcircle :
      p ∈ circleSet ExplicitInputs.karlssonOEISQ0.center
        ExplicitInputs.karlssonOEISQ0.radius)
    (hray :
      p ∈ raySet ExplicitInputs.karlssonOEISQ1.anchor
        ExplicitInputs.karlssonOEISQ1.rayDirection) :
    False := by
  have hp_lift :
      toEuclideanR2 p ∈
        euclideanCircleRaySet ExplicitInputs.karlssonOEISQ0
          ExplicitInputs.karlssonOEISQ1 := by
    constructor
    · exact
        (mem_circleSet_iff_mem_euclideanSphere
          ExplicitInputs.karlssonOEISQ0.radius_pos.le).1
          hcircle
    · exact
        (mem_raySet_iff_mem_euclideanRaySet
          (p := p)
          (anchor := ExplicitInputs.karlssonOEISQ1.anchor)
          (direction := ExplicitInputs.karlssonOEISQ1.rayDirection)).1
          hray
  exact ExplicitInputs.karlssonOEISQ0_Q1_circleRaySet_empty
    (toEuclideanR2 p) hp_lift

theorem q0q1RayRay_eq_of_mem
    {p : PrimitiveGeometry.R2}
    (hray0 :
      p ∈ raySet ExplicitInputs.karlssonOEISQ0.anchor
        ExplicitInputs.karlssonOEISQ0.rayDirection)
    (hray1 :
      p ∈ raySet ExplicitInputs.karlssonOEISQ1.anchor
        ExplicitInputs.karlssonOEISQ1.rayDirection) :
    p = q0q1RayRayPoint := by
  have hp_lift :
      toEuclideanR2 p ∈
        euclideanRayRaySet ExplicitInputs.karlssonOEISQ0
          ExplicitInputs.karlssonOEISQ1 := by
    constructor
    · exact
        (mem_raySet_iff_mem_euclideanRaySet
          (p := p)
          (anchor := ExplicitInputs.karlssonOEISQ0.anchor)
          (direction := ExplicitInputs.karlssonOEISQ0.rayDirection)).1
          hray0
    · exact
        (mem_raySet_iff_mem_euclideanRaySet
          (p := p)
          (anchor := ExplicitInputs.karlssonOEISQ1.anchor)
          (direction := ExplicitInputs.karlssonOEISQ1.rayDirection)).1
          hray1
  exact toEuclideanR2_injective
    (eq_of_mem_euclideanRayRaySet_of_rayLine_ne
      ExplicitInputs.karlssonOEISQ0_Q1_rayLines_distinct
      hp_lift q0q1RayRayPoint_mem_euclideanRayRaySet)

/-- Component classification for the primitive `(Q0,Q1)` carrier
intersection. -/
theorem q0q1PairIntersection_eq_fivePoint_of_mem
    {p : PrimitiveGeometry.R2}
    (hp :
      p ∈ pairIntersectionSet ExplicitInputs.karlssonOEISQ0
        ExplicitInputs.karlssonOEISQ1) :
    p = q0q1RayRayPoint ∨
      p = q0q1RayCircleLeftPoint ∨
        p = q0q1RayCircleRightPoint ∨
          p = q0q1CircleCircleUpperPoint ∨
            p = q0q1CircleCircleLowerPoint := by
  rcases hp with ⟨hp0, hp1⟩
  rcases hp0 with hcircle0 | hray0
  · rcases hp1 with hcircle1 | hray1
    · rcases q0q1CircleCircle_eq_upper_or_lower_of_mem hcircle0 hcircle1 with
        hupper | hlower
      · exact Or.inr (Or.inr (Or.inr (Or.inl hupper)))
      · exact Or.inr (Or.inr (Or.inr (Or.inr hlower)))
    · exact False.elim (q0q1CircleRay_false_of_mem hcircle0 hray1)
  · rcases hp1 with hcircle1 | hray1
    · rcases q0q1RayCircle_eq_left_or_right_of_mem hray0 hcircle1 with
        hleft | hright
      · exact Or.inr (Or.inl hleft)
      · exact Or.inr (Or.inr (Or.inl hright))
    · exact Or.inl (q0q1RayRay_eq_of_mem hray0 hray1)

/-- The five-point finset is exactly the primitive `(Q0,Q1)` carrier
intersection. -/
theorem q0q1FivePointFinset_spec :
    (q0q1FivePointFinset : Set PrimitiveGeometry.R2) =
      pairIntersectionSet ExplicitInputs.karlssonOEISQ0
        ExplicitInputs.karlssonOEISQ1 := by
  ext p
  constructor
  · intro hp
    simp [q0q1FivePointFinset] at hp
    rcases hp with rfl | rfl | rfl | rfl | rfl
    · exact q0q1RayRayPoint_mem_pairIntersectionSet
    · exact q0q1RayCircleLeftPoint_mem_pairIntersectionSet
    · exact q0q1RayCircleRightPoint_mem_pairIntersectionSet
    · exact q0q1CircleCircleUpperPoint_mem_pairIntersectionSet
    · exact q0q1CircleCircleLowerPoint_mem_pairIntersectionSet
  · intro hp
    rcases q0q1PairIntersection_eq_fivePoint_of_mem hp with
      h | h | h | h | h
    all_goals
      subst p
      simp [q0q1FivePointFinset]

theorem pair01_crossingPoints_card_eq_five
    (C : ExplicitInputs.KarlssonOEISBaseSixPairCoordinateCrossingCertificate) :
    C.pair01.crossingPoints.card = 5 := by
  exact le_antisymm C.zero_one_card_le_five
    (pair01_crossingPoints_five_le_card C)

theorem pair01_crossingPoints_eq_fivePointFinset
    (C : ExplicitInputs.KarlssonOEISBaseSixPairCoordinateCrossingCertificate) :
    C.pair01.crossingPoints = q0q1FivePointFinset := by
  apply Finset.ext
  intro p
  have hset :
      ((C.pair01.crossingPoints : Finset PrimitiveGeometry.R2) :
          Set PrimitiveGeometry.R2) =
        (q0q1FivePointFinset : Set PrimitiveGeometry.R2) := by
    rw [C.pair01.crossingPoints_spec]
    simpa [EuclideanLollipopArrangement.pairIntersectionSet] using
      q0q1FivePointFinset_spec.symm
  change
    p ∈
        ((C.pair01.crossingPoints : Finset PrimitiveGeometry.R2) :
          Set PrimitiveGeometry.R2) ↔
      p ∈ (q0q1FivePointFinset : Set PrimitiveGeometry.R2)
  rw [hset]

/-- The exceptional OEIS/Karlsson pair certificate can now be built directly
from the five exact points. -/
noncomputable def q0q1PairCoordinateCrossingCertificate :
    ExplicitInputs.KarlssonOEISBasePairCoordinateCrossingCertificate
      (0 : Fin 4) (1 : Fin 4) (by decide) where
  crossingPoints := q0q1FivePointFinset
  crossingPoints_spec := by
    simpa [EuclideanLollipopArrangement.pairIntersectionSet] using
      q0q1FivePointFinset_spec
  cross_eq_card := by
    rw [q0q1FivePointFinset_card]
    norm_num

end

end OEISGeometry

end CompleteFormalization
end TheoremOneManuscript
end Lollipop
