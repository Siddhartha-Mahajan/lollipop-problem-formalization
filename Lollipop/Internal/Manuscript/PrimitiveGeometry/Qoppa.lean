import Lollipop.Internal.Manuscript.PrimitiveGeometry.Basic
import Mathlib.Analysis.Real.Pi.Bounds

/-!
Coordinate constructors for lollipops/qoppas.

The OEIS/Karlsson data list lollipops either by center or by anchor together
with a radius and a bearing angle.  This file formalizes those two
constructors for the primitive lollipop model.  The only trigonometry needed
is the mathlib identity `cos^2 + sin^2 = 1`, which proves that the anchor
lies on the specified circle.
-/

namespace Lollipop
namespace TheoremOneManuscript
namespace PrimitiveGeometry

open TheoremOneEndToEnd.PaulsenLinearAlgebra

/-- A point/vector in the primitive coordinate plane. -/
def point2 (x y : ℝ) : R2
  | 0 => x
  | 1 => y

@[simp] theorem point2_zero (x y : ℝ) :
    point2 x y 0 = x := rfl

@[simp] theorem point2_one (x y : ℝ) :
    point2 x y 1 = y := rfl

/-- Unit direction vector with bearing angle `theta`. -/
noncomputable def angleDirection (theta : ℝ) : R2 :=
  point2 (Real.cos theta) (Real.sin theta)

@[simp] theorem angleDirection_zero (theta : ℝ) :
    angleDirection theta 0 = Real.cos theta := rfl

@[simp] theorem angleDirection_one (theta : ℝ) :
    angleDirection theta 1 = Real.sin theta := rfl

/-- A bearing direction has squared norm `1`. -/
theorem normSq2_angleDirection (theta : ℝ) :
    normSq2 (angleDirection theta) = 1 := by
  unfold normSq2 dot2 angleDirection point2
  nlinarith [Real.cos_sq_add_sin_sq theta]

/-- A bearing direction is nonzero. -/
theorem angleDirection_ne_zero (theta : ℝ) :
    angleDirection theta ≠ 0 := by
  intro hzero
  have hnorm := normSq2_angleDirection theta
  rw [hzero] at hnorm
  norm_num [normSq2, dot2] at hnorm

/-- If the anchor is `center + radius * direction(theta)`, then it lies on
the circle of radius `radius` around `center`. -/
theorem center_plus_radius_direction_mem_circleSet
    (center : R2) (radius theta : ℝ) :
    center + radius • angleDirection theta ∈ circleSet center radius := by
  unfold circleSet distSq2 normSq2 dot2 angleDirection point2
  simp [Pi.add_apply, Pi.sub_apply, Pi.smul_apply]
  nlinarith [Real.cos_sq_add_sin_sq theta]

/-- If the center is `anchor - radius * direction(theta)`, then the anchor
lies on that circle. -/
theorem anchor_mem_circleSet_anchor_minus_radius_direction
    (anchor : R2) (radius theta : ℝ) :
    anchor ∈ circleSet (anchor - radius • angleDirection theta) radius := by
  unfold circleSet distSq2 normSq2 dot2 angleDirection point2
  simp [Pi.sub_apply, Pi.smul_apply]
  nlinarith [Real.cos_sq_add_sin_sq theta]

namespace EuclideanLollipop

/-- Constructor matching `Qoppa.from_center(center, radius, theta)`: the
anchor is `center + radius * (cos theta, sin theta)`, and the ray points in
that bearing direction. -/
noncomputable def fromCenter
    (center : R2) (radius theta normalizedDirection : ℝ)
    (hradius : 0 < radius)
    (hdir_nonneg : 0 ≤ normalizedDirection)
    (hdir_lt_one : normalizedDirection < 1) :
    EuclideanLollipop where
  center := center
  radius := radius
  radius_pos := hradius
  anchor := center + radius • angleDirection theta
  rayDirection := angleDirection theta
  rayDirection_ne_zero := angleDirection_ne_zero theta
  anchor_on_circle :=
    center_plus_radius_direction_mem_circleSet center radius theta
  normalizedDirection := normalizedDirection
  normalizedDirection_nonneg := hdir_nonneg
  normalizedDirection_lt_one := hdir_lt_one

/-- The `fromCenter` constructor satisfies the manuscript's radial-outward
stem condition. -/
theorem fromCenter_isRadialOutward
    (center : R2) (radius theta normalizedDirection : ℝ)
    (hradius : 0 < radius)
    (hdir_nonneg : 0 ≤ normalizedDirection)
    (hdir_lt_one : normalizedDirection < 1) :
    (fromCenter center radius theta normalizedDirection
      hradius hdir_nonneg hdir_lt_one).IsRadialOutward := by
  refine ⟨radius, hradius, ?_⟩
  ext i
  simp [fromCenter, Pi.add_apply, Pi.sub_apply, Pi.smul_apply]

/-- Constructor matching `Qoppa.from_anchor(anchor, radius, theta)`: the
center is `anchor - radius * (cos theta, sin theta)`, and the ray points in
that bearing direction. -/
noncomputable def fromAnchor
    (anchor : R2) (radius theta normalizedDirection : ℝ)
    (hradius : 0 < radius)
    (hdir_nonneg : 0 ≤ normalizedDirection)
    (hdir_lt_one : normalizedDirection < 1) :
    EuclideanLollipop where
  center := anchor - radius • angleDirection theta
  radius := radius
  radius_pos := hradius
  anchor := anchor
  rayDirection := angleDirection theta
  rayDirection_ne_zero := angleDirection_ne_zero theta
  anchor_on_circle :=
    anchor_mem_circleSet_anchor_minus_radius_direction anchor radius theta
  normalizedDirection := normalizedDirection
  normalizedDirection_nonneg := hdir_nonneg
  normalizedDirection_lt_one := hdir_lt_one

/-- The `fromAnchor` constructor satisfies the manuscript's radial-outward
stem condition. -/
theorem fromAnchor_isRadialOutward
    (anchor : R2) (radius theta normalizedDirection : ℝ)
    (hradius : 0 < radius)
    (hdir_nonneg : 0 ≤ normalizedDirection)
    (hdir_lt_one : normalizedDirection < 1) :
    (fromAnchor anchor radius theta normalizedDirection
      hradius hdir_nonneg hdir_lt_one).IsRadialOutward := by
  refine ⟨radius, hradius, ?_⟩
  ext i
  simp [fromAnchor, Pi.sub_apply, Pi.smul_apply]

end EuclideanLollipop

end PrimitiveGeometry
end TheoremOneManuscript
end Lollipop
