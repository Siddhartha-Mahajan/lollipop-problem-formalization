import Lollipop.Internal.Manuscript.PrimitiveGeometry.Basic
import Mathlib.Geometry.Euclidean.Sphere.Power
import Mathlib.Geometry.Euclidean.Sphere.SecondInter

/-!
Bridge from primitive coordinate circles to mathlib Euclidean spheres.

The primitive lollipop layer records points as `Fin 2 -> ℝ` because Paulsen's
linear-algebra appendix uses explicit coordinates.  Mathlib's Euclidean
line/sphere theorems use the `L^2` product space `EuclideanSpace ℝ (Fin 2)`.
This file connects the two views by the canonical `WithLp.toLp 2` wrapper and
proves that the primitive squared-distance circle is exactly the preimage of a
mathlib Euclidean sphere.
-/

namespace Lollipop
namespace TheoremOneManuscript
namespace PrimitiveGeometry

open TheoremOneEndToEnd.PaulsenLinearAlgebra

/-- The same coordinate plane as `R2`, equipped with mathlib's `L^2`
inner-product norm. -/
abbrev EuclideanR2 : Type :=
  EuclideanSpace ℝ (Fin 2)

/-- View the primitive coordinate plane as mathlib's Euclidean plane. -/
def toEuclideanR2 (x : R2) : EuclideanR2 :=
  WithLp.toLp 2 x

/-- The lift from primitive coordinates to `EuclideanSpace` is injective. -/
theorem toEuclideanR2_injective : Function.Injective toEuclideanR2 := by
  intro x y hxy
  exact WithLp.toLp_injective 2 hxy

@[simp]
theorem toEuclideanR2_apply (x : R2) (i : Fin 2) :
    toEuclideanR2 x i = x i :=
  rfl

@[simp]
theorem toEuclideanR2_add (x y : R2) :
    toEuclideanR2 (x + y) = toEuclideanR2 x + toEuclideanR2 y := by
  ext i
  rfl

@[simp]
theorem toEuclideanR2_smul (t : ℝ) (x : R2) :
    toEuclideanR2 (t • x) = t • toEuclideanR2 x := by
  ext i
  rfl

@[simp]
theorem toEuclideanR2_sub (x y : R2) :
    toEuclideanR2 (x - y) = toEuclideanR2 x - toEuclideanR2 y := by
  ext i
  rfl

/-- The explicit squared distance used in Paulsen's coordinate calculations is
the squared `L^2` distance after lifting to `EuclideanSpace`. -/
theorem distSq2_eq_euclidean_dist_sq (x y : R2) :
    distSq2 x y = dist (toEuclideanR2 x) (toEuclideanR2 y) ^ 2 := by
  calc
    distSq2 x y =
        (x 0 - y 0) ^ 2 + (x 1 - y 1) ^ 2 := by
          unfold distSq2 normSq2 dot2
          simp [Pi.sub_apply]
          ring
    _ = ∑ i : Fin 2, dist (toEuclideanR2 x i) (toEuclideanR2 y i) ^ 2 := by
          simp [Fin.sum_univ_two, Real.dist_eq, sq_abs]
    _ = dist (toEuclideanR2 x) (toEuclideanR2 y) ^ 2 := by
          exact (EuclideanSpace.dist_sq_eq (toEuclideanR2 x) (toEuclideanR2 y)).symm

/-- The oriented two-dimensional determinant in the primitive coordinate
model. -/
def det2 (x y : R2) : ℝ :=
  x 0 * y 1 - x 1 * y 0

/-- The two-dimensional Lagrange identity:
`|x|^2 |y|^2 = <x,y>^2 + det(x,y)^2`. -/
theorem normSq2_mul_normSq2_eq_dot2_sq_add_det2_sq
    (x y : R2) :
    normSq2 x * normSq2 y = dot2 x y ^ 2 + det2 x y ^ 2 := by
  unfold normSq2 dot2 det2
  ring

/-- The squared determinant is bounded by the product of squared norms. -/
theorem det2_sq_le_normSq2_mul_normSq2 (x y : R2) :
    det2 x y ^ 2 ≤ normSq2 x * normSq2 y := by
  have h := normSq2_mul_normSq2_eq_dot2_sq_add_det2_sq x y
  nlinarith [sq_nonneg (dot2 x y)]

/-- Moving along a line in direction `v` does not change the determinant
against `v`. -/
theorem det2_line_vadd_sub_right
    (anchor center direction : R2) (t : ℝ) :
    det2 ((anchor + t • direction) - center) direction =
      det2 (anchor - center) direction := by
  unfold det2
  simp [Pi.add_apply, Pi.sub_apply, Pi.smul_apply]
  ring

/-- Squared distance from a center after moving by `t` along a primitive
direction. -/
theorem distSq2_vadd_smul_sub
    (anchor center direction : R2) (t : ℝ) :
    distSq2 (anchor + t • direction) center =
      distSq2 anchor center +
        2 * t * dot2 (anchor - center) direction +
        t ^ 2 * normSq2 direction := by
  unfold distSq2 normSq2 dot2
  simp [Pi.add_apply, Pi.sub_apply, Pi.smul_apply]
  ring

/-- In the primitive coordinate plane, zero determinant with a nonzero first
vector means the second vector is a scalar multiple of the first. -/
theorem exists_smul_eq_of_det2_eq_zero_of_ne_zero
    {v w : R2} (hv : v ≠ 0) (hdet : det2 v w = 0) :
    ∃ c : ℝ, w = c • v := by
  by_cases hv0 : v 0 = 0
  · have hv1 : v 1 ≠ 0 := by
      intro hv1
      apply hv
      ext i
      fin_cases i <;> simp [hv0, hv1]
    have hw0 : w 0 = 0 := by
      have hmul : v 1 * w 0 = 0 := by
        have hneg : -(v 1 * w 0) = 0 := by
          simpa [det2, hv0] using hdet
        exact neg_eq_zero.mp hneg
      exact (mul_eq_zero.mp hmul).resolve_left hv1
    refine ⟨w 1 / v 1, ?_⟩
    ext i
    fin_cases i
    · simp [hw0, hv0]
    · simp [Pi.smul_apply]
      field_simp [hv1]
  · have hcoord : v 0 * w 1 = v 1 * w 0 := by
      unfold det2 at hdet
      nlinarith
    refine ⟨w 0 / v 0, ?_⟩
    ext i
    fin_cases i
    · simp [Pi.smul_apply]
      field_simp [hv0]
    · simp [Pi.smul_apply]
      field_simp [hv0]
      nlinarith

/-- The mathlib Euclidean sphere corresponding to a primitive coordinate
circle. -/
def euclideanSphere (center : R2) (radius : ℝ) :
    EuclideanGeometry.Sphere EuclideanR2 where
  center := toEuclideanR2 center
  radius := radius

/-- Two lifted primitive coordinate spheres are different exactly when their
primitive centers or radii are different. -/
theorem euclideanSphere_ne_iff
    {center₁ center₂ : R2} {radius₁ radius₂ : ℝ} :
    euclideanSphere center₁ radius₁ ≠ euclideanSphere center₂ radius₂ ↔
      center₁ ≠ center₂ ∨ radius₁ ≠ radius₂ := by
  rw [EuclideanGeometry.Sphere.ne_iff]
  constructor
  · rintro (hcenter | hradius)
    · exact Or.inl fun h => hcenter (by simp [euclideanSphere, h])
    · exact Or.inr hradius
  · rintro (hcenter | hradius)
    · exact Or.inl fun h => hcenter (toEuclideanR2_injective h)
    · exact Or.inr hradius

/-- Unequal primitive centers give unequal lifted spheres. -/
theorem euclideanSphere_ne_of_center_ne
    {center₁ center₂ : R2} {radius₁ radius₂ : ℝ}
    (hcenter : center₁ ≠ center₂) :
    euclideanSphere center₁ radius₁ ≠ euclideanSphere center₂ radius₂ :=
  euclideanSphere_ne_iff.2 (Or.inl hcenter)

/-- Unequal radii give unequal lifted spheres. -/
theorem euclideanSphere_ne_of_radius_ne
    {center₁ center₂ : R2} {radius₁ radius₂ : ℝ}
    (hradius : radius₁ ≠ radius₂) :
    euclideanSphere center₁ radius₁ ≠ euclideanSphere center₂ radius₂ :=
  euclideanSphere_ne_iff.2 (Or.inr hradius)

/-- Membership in the primitive squared-coordinate circle is exactly
membership in the corresponding mathlib Euclidean sphere, for nonnegative
radii. -/
theorem mem_circleSet_iff_mem_euclideanSphere
    {p center : R2} {radius : ℝ} (hradius : 0 ≤ radius) :
    p ∈ circleSet center radius ↔
      toEuclideanR2 p ∈ euclideanSphere center radius := by
  unfold circleSet euclideanSphere
  rw [EuclideanGeometry.mem_sphere]
  constructor
  · intro hp
    have hsq :
        dist (toEuclideanR2 p) (toEuclideanR2 center) ^ 2 = radius ^ 2 := by
      rw [← distSq2_eq_euclidean_dist_sq]
      exact hp
    exact (sq_eq_sq₀ dist_nonneg hradius).1 hsq
  · intro hp
    have hp' : dist (toEuclideanR2 p) (toEuclideanR2 center) = radius := by
      simpa using hp
    show distSq2 p center = radius ^ 2
    rw [distSq2_eq_euclidean_dist_sq, hp']

/-- Set-level version of `mem_circleSet_iff_mem_euclideanSphere`. -/
theorem circleSet_eq_preimage_euclideanSphere
    (center : R2) {radius : ℝ} (hradius : 0 ≤ radius) :
    circleSet center radius =
      {p : R2 | toEuclideanR2 p ∈ euclideanSphere center radius} := by
  ext p
  exact mem_circleSet_iff_mem_euclideanSphere (p := p) hradius

/-- The primitive ray, lifted to mathlib's Euclidean plane. -/
def euclideanRaySet (anchor direction : R2) : Set EuclideanR2 :=
  {p | ∃ t : ℝ, 0 ≤ t ∧ p = toEuclideanR2 anchor + t • toEuclideanR2 direction}

/-- Membership in a primitive ray is exactly membership in the corresponding
lifted Euclidean ray. -/
theorem mem_raySet_iff_mem_euclideanRaySet {p anchor direction : R2} :
    p ∈ raySet anchor direction ↔
      toEuclideanR2 p ∈ euclideanRaySet anchor direction := by
  unfold raySet euclideanRaySet
  constructor
  · rintro ⟨t, ht, rfl⟩
    exact ⟨t, ht, by simp⟩
  · rintro ⟨t, ht, hp⟩
    refine ⟨t, ht, ?_⟩
    apply WithLp.toLp_injective 2
    simpa [toEuclideanR2] using hp

/-- Set-level version of `mem_raySet_iff_mem_euclideanRaySet`. -/
theorem raySet_eq_preimage_euclideanRaySet (anchor direction : R2) :
    raySet anchor direction =
      {p : R2 | toEuclideanR2 p ∈ euclideanRaySet anchor direction} := by
  ext p
  exact mem_raySet_iff_mem_euclideanRaySet

/-- The supporting affine line of a lifted lollipop ray. -/
noncomputable def euclideanRayLine (L : EuclideanLollipop) :
    AffineSubspace ℝ EuclideanR2 :=
  line[ℝ, toEuclideanR2 L.anchor,
    toEuclideanR2 L.rayDirection +ᵥ toEuclideanR2 L.anchor]

/-- The lifted anchor lies on its ray's supporting affine line. -/
theorem anchor_mem_euclideanRayLine (L : EuclideanLollipop) :
    toEuclideanR2 L.anchor ∈ euclideanRayLine L := by
  unfold euclideanRayLine
  exact left_mem_affineSpan_pair ℝ _ _

/-- The endpoint obtained by adding one direction vector lies on the ray's
supporting affine line. -/
theorem direction_vadd_anchor_mem_euclideanRayLine (L : EuclideanLollipop) :
    toEuclideanR2 L.rayDirection +ᵥ toEuclideanR2 L.anchor ∈
      euclideanRayLine L := by
  unfold euclideanRayLine
  exact right_mem_affineSpan_pair ℝ _ _

/-- The direction of the supporting affine line of a lifted ray. -/
theorem euclideanRayLine_direction (L : EuclideanLollipop) :
    (euclideanRayLine L).direction =
      ℝ ∙ toEuclideanR2 L.rayDirection := by
  unfold euclideanRayLine
  rw [direction_affineSpan, vectorSpan_pair_rev]
  simp [vsub_eq_sub, vadd_eq_add]

/-- The supporting-line definition agrees with the `mk'` line used by
mathlib's line/sphere intersection theorem. -/
theorem euclideanRayLine_eq_mk' (L : EuclideanLollipop) :
    euclideanRayLine L =
      AffineSubspace.mk' (toEuclideanR2 L.anchor)
        (ℝ ∙ toEuclideanR2 L.rayDirection) := by
  have hmk :
      AffineSubspace.mk' (toEuclideanR2 L.anchor)
          (euclideanRayLine L).direction =
        euclideanRayLine L :=
    AffineSubspace.mk'_eq (anchor_mem_euclideanRayLine L)
  rw [← hmk, euclideanRayLine_direction]

/-- If one ray anchor does not lie on another ray's supporting line, the two
supporting lines are different. -/
theorem euclideanRayLine_ne_of_anchor_notMem
    {L M : EuclideanLollipop}
    (hanchor : toEuclideanR2 L.anchor ∉ euclideanRayLine M) :
    euclideanRayLine L ≠ euclideanRayLine M := by
  intro hline
  exact hanchor (by simpa [hline] using anchor_mem_euclideanRayLine L)

/-- Nonparallel primitive ray directions give distinct lifted supporting
lines.  This is a convenient coordinate route for discharging the generic
ray-line noncoincidence field in carrier-counting certificates. -/
theorem euclideanRayLine_ne_of_det2_rayDirection_ne_zero
    {L M : EuclideanLollipop}
    (hdet : det2 L.rayDirection M.rayDirection ≠ 0) :
    euclideanRayLine L ≠ euclideanRayLine M := by
  intro hline
  have hdir :
      ℝ ∙ toEuclideanR2 L.rayDirection =
        ℝ ∙ toEuclideanR2 M.rayDirection := by
    have hcongr := congrArg AffineSubspace.direction hline
    simpa [euclideanRayLine_direction] using hcongr
  have hmem :
      toEuclideanR2 M.rayDirection ∈
        ℝ ∙ toEuclideanR2 L.rayDirection := by
    rw [hdir]
    exact Submodule.mem_span_singleton_self (toEuclideanR2 M.rayDirection)
  rcases Submodule.mem_span_singleton.mp hmem with ⟨c, hc⟩
  have hMdir : M.rayDirection = c • L.rayDirection := by
    apply toEuclideanR2_injective
    calc
      toEuclideanR2 M.rayDirection = c • toEuclideanR2 L.rayDirection :=
        hc.symm
      _ = toEuclideanR2 (c • L.rayDirection) := by simp
  have hzero : det2 L.rayDirection M.rayDirection = 0 := by
    rw [hMdir]
    unfold det2
    simp [Pi.smul_apply]
    ring
  exact hdet hzero

/-- The lifted carrier of a primitive lollipop. -/
def euclideanCarrier (L : EuclideanLollipop) : Set EuclideanR2 :=
  (euclideanSphere L.center L.radius : Set EuclideanR2) ∪
    euclideanRaySet L.anchor L.rayDirection

/-- Lifted intersection set of two primitive lollipop carriers. -/
def euclideanPairIntersectionSet (L M : EuclideanLollipop) : Set EuclideanR2 :=
  euclideanCarrier L ∩ euclideanCarrier M

/-- Lifted pairwise carrier intersection is symmetric. -/
theorem euclideanPairIntersectionSet_symm (L M : EuclideanLollipop) :
    euclideanPairIntersectionSet L M = euclideanPairIntersectionSet M L := by
  ext p
  constructor
  · intro hp
    exact ⟨hp.2, hp.1⟩
  · intro hp
    exact ⟨hp.2, hp.1⟩

/-- Lifted circle-circle component of a carrier intersection. -/
def euclideanCircleCircleSet (L M : EuclideanLollipop) : Set EuclideanR2 :=
  (euclideanSphere L.center L.radius : Set EuclideanR2) ∩
    (euclideanSphere M.center M.radius : Set EuclideanR2)

/-- Lifted circle-ray component of a carrier intersection. -/
def euclideanCircleRaySet (L M : EuclideanLollipop) : Set EuclideanR2 :=
  (euclideanSphere L.center L.radius : Set EuclideanR2) ∩
    euclideanRaySet M.anchor M.rayDirection

/-- Lifted ray-circle component of a carrier intersection. -/
def euclideanRayCircleSet (L M : EuclideanLollipop) : Set EuclideanR2 :=
  euclideanRaySet L.anchor L.rayDirection ∩
    (euclideanSphere M.center M.radius : Set EuclideanR2)

/-- Lifted ray-ray component of a carrier intersection. -/
def euclideanRayRaySet (L M : EuclideanLollipop) : Set EuclideanR2 :=
  euclideanRaySet L.anchor L.rayDirection ∩
    euclideanRaySet M.anchor M.rayDirection

/-- Primitive circle memberships lift to the Euclidean circle-circle
component. -/
theorem mem_euclideanCircleCircleSet_of_mem_circleSets
    {L M : EuclideanLollipop} {p : R2}
    (hL : p ∈ circleSet L.center L.radius)
    (hM : p ∈ circleSet M.center M.radius) :
    toEuclideanR2 p ∈ euclideanCircleCircleSet L M := by
  constructor
  · exact (mem_circleSet_iff_mem_euclideanSphere
      (p := p) (center := L.center) (radius := L.radius)
      L.radius_pos.le).1 hL
  · exact (mem_circleSet_iff_mem_euclideanSphere
      (p := p) (center := M.center) (radius := M.radius)
      M.radius_pos.le).1 hM

/-- Primitive circle/ray memberships lift to the Euclidean circle-ray
component. -/
theorem mem_euclideanCircleRaySet_of_mem_circleSet_of_mem_raySet
    {L M : EuclideanLollipop} {p : R2}
    (hL : p ∈ circleSet L.center L.radius)
    (hM : p ∈ raySet M.anchor M.rayDirection) :
    toEuclideanR2 p ∈ euclideanCircleRaySet L M := by
  constructor
  · exact (mem_circleSet_iff_mem_euclideanSphere
      (p := p) (center := L.center) (radius := L.radius)
      L.radius_pos.le).1 hL
  · exact (mem_raySet_iff_mem_euclideanRaySet
      (p := p) (anchor := M.anchor) (direction := M.rayDirection)).1 hM

/-- Primitive ray/circle memberships lift to the Euclidean ray-circle
component. -/
theorem mem_euclideanRayCircleSet_of_mem_raySet_of_mem_circleSet
    {L M : EuclideanLollipop} {p : R2}
    (hL : p ∈ raySet L.anchor L.rayDirection)
    (hM : p ∈ circleSet M.center M.radius) :
    toEuclideanR2 p ∈ euclideanRayCircleSet L M := by
  constructor
  · exact (mem_raySet_iff_mem_euclideanRaySet
      (p := p) (anchor := L.anchor) (direction := L.rayDirection)).1 hL
  · exact (mem_circleSet_iff_mem_euclideanSphere
      (p := p) (center := M.center) (radius := M.radius)
      M.radius_pos.le).1 hM

/-- Primitive ray memberships lift to the Euclidean ray-ray component. -/
theorem mem_euclideanRayRaySet_of_mem_raySets
    {L M : EuclideanLollipop} {p : R2}
    (hL : p ∈ raySet L.anchor L.rayDirection)
    (hM : p ∈ raySet M.anchor M.rayDirection) :
    toEuclideanR2 p ∈ euclideanRayRaySet L M := by
  constructor
  · exact (mem_raySet_iff_mem_euclideanRaySet
      (p := p) (anchor := L.anchor) (direction := L.rayDirection)).1 hL
  · exact (mem_raySet_iff_mem_euclideanRaySet
      (p := p) (anchor := M.anchor) (direction := M.rayDirection)).1 hM

/-- If the distance between two circle centers is greater than the sum of the
radii, their lifted circle-circle component is empty. -/
theorem euclideanCircleCircleSet_empty_of_radius_add_lt_dist
    {L M : EuclideanLollipop}
    (hfar :
      L.radius + M.radius <
        dist (toEuclideanR2 L.center) (toEuclideanR2 M.center)) :
    ∀ p : EuclideanR2, p ∉ euclideanCircleCircleSet L M := by
  intro p hp
  have hpL :
      dist p (toEuclideanR2 L.center) = L.radius :=
    EuclideanGeometry.mem_sphere.1 hp.1
  have hpM :
      dist p (toEuclideanR2 M.center) = M.radius :=
    EuclideanGeometry.mem_sphere.1 hp.2
  have htri :
      dist (toEuclideanR2 L.center) (toEuclideanR2 M.center) ≤
        dist (toEuclideanR2 L.center) p +
          dist p (toEuclideanR2 M.center) :=
    dist_triangle _ _ _
  rw [dist_comm (toEuclideanR2 L.center) p, hpL, hpM] at htri
  linarith

/-- Squared-coordinate version of the far-apart circle emptiness criterion. -/
theorem euclideanCircleCircleSet_empty_of_radius_add_sq_lt_distSq2
    {L M : EuclideanLollipop}
    (hfar :
      (L.radius + M.radius) ^ 2 < distSq2 L.center M.center) :
    ∀ p : EuclideanR2, p ∉ euclideanCircleCircleSet L M := by
  have hsum_nonneg : 0 ≤ L.radius + M.radius :=
    add_nonneg L.radius_pos.le M.radius_pos.le
  have hfar_euclidean :
      (L.radius + M.radius) ^ 2 <
        dist (toEuclideanR2 L.center) (toEuclideanR2 M.center) ^ 2 := by
    rwa [distSq2_eq_euclidean_dist_sq] at hfar
  have hdist :
      L.radius + M.radius <
        dist (toEuclideanR2 L.center) (toEuclideanR2 M.center) := by
    exact (sq_lt_sq₀ hsum_nonneg dist_nonneg).1 hfar_euclidean
  exact euclideanCircleCircleSet_empty_of_radius_add_lt_dist hdist

/-- If one circle lies strictly inside the other, with center distance plus
the smaller radius less than the larger radius, then the lifted circle-circle
component is empty. -/
theorem euclideanCircleCircleSet_empty_of_dist_add_left_radius_lt_right_radius
    {L M : EuclideanLollipop}
    (hcontained :
      dist (toEuclideanR2 L.center) (toEuclideanR2 M.center) + L.radius <
        M.radius) :
    ∀ p : EuclideanR2, p ∉ euclideanCircleCircleSet L M := by
  intro p hp
  have hpL :
      dist p (toEuclideanR2 L.center) = L.radius :=
    EuclideanGeometry.mem_sphere.1 hp.1
  have hpM :
      dist p (toEuclideanR2 M.center) = M.radius :=
    EuclideanGeometry.mem_sphere.1 hp.2
  have htri :
      dist p (toEuclideanR2 M.center) ≤
        dist p (toEuclideanR2 L.center) +
          dist (toEuclideanR2 L.center) (toEuclideanR2 M.center) :=
    dist_triangle _ _ _
  rw [hpL, hpM] at htri
  linarith

/-- Symmetric strictly-contained circle emptiness criterion. -/
theorem euclideanCircleCircleSet_empty_of_dist_add_right_radius_lt_left_radius
    {L M : EuclideanLollipop}
    (hcontained :
      dist (toEuclideanR2 L.center) (toEuclideanR2 M.center) + M.radius <
        L.radius) :
    ∀ p : EuclideanR2, p ∉ euclideanCircleCircleSet L M := by
  intro p hp
  have hempty :
      ∀ p : EuclideanR2, p ∉ euclideanCircleCircleSet M L :=
    euclideanCircleCircleSet_empty_of_dist_add_left_radius_lt_right_radius
      (L := M) (M := L) (by
        rw [dist_comm]
        exact hcontained)
  exact hempty p ⟨hp.2, hp.1⟩

/-- Squared-coordinate strictly-contained criterion with `L` inside `M`. -/
theorem euclideanCircleCircleSet_empty_of_distSq2_lt_right_sub_left_radius_sq
    {L M : EuclideanLollipop}
    (hradius : L.radius < M.radius)
    (hcontained :
      distSq2 L.center M.center < (M.radius - L.radius) ^ 2) :
    ∀ p : EuclideanR2, p ∉ euclideanCircleCircleSet L M := by
  have hdiff_nonneg : 0 ≤ M.radius - L.radius := by
    linarith
  have hdist_sq :
      dist (toEuclideanR2 L.center) (toEuclideanR2 M.center) ^ 2 <
        (M.radius - L.radius) ^ 2 := by
    simpa [distSq2_eq_euclidean_dist_sq] using hcontained
  have hdist :
      dist (toEuclideanR2 L.center) (toEuclideanR2 M.center) <
        M.radius - L.radius := by
    exact (sq_lt_sq₀ dist_nonneg hdiff_nonneg).1 hdist_sq
  exact
    euclideanCircleCircleSet_empty_of_dist_add_left_radius_lt_right_radius
      (by linarith)

/-- Squared-coordinate strictly-contained criterion with `M` inside `L`. -/
theorem euclideanCircleCircleSet_empty_of_distSq2_lt_left_sub_right_radius_sq
    {L M : EuclideanLollipop}
    (hradius : M.radius < L.radius)
    (hcontained :
      distSq2 L.center M.center < (L.radius - M.radius) ^ 2) :
    ∀ p : EuclideanR2, p ∉ euclideanCircleCircleSet L M := by
  have hdiff_nonneg : 0 ≤ L.radius - M.radius := by
    linarith
  have hdist_sq :
      dist (toEuclideanR2 L.center) (toEuclideanR2 M.center) ^ 2 <
        (L.radius - M.radius) ^ 2 := by
    simpa [distSq2_eq_euclidean_dist_sq] using hcontained
  have hdist :
      dist (toEuclideanR2 L.center) (toEuclideanR2 M.center) <
        L.radius - M.radius := by
    exact (sq_lt_sq₀ dist_nonneg hdiff_nonneg).1 hdist_sq
  exact
    euclideanCircleCircleSet_empty_of_dist_add_right_radius_lt_left_radius
      (by linarith)

/-- A concrete certificate that the two primitive circles do not meet.  The
squared constructors match the coordinate inequalities used elsewhere in the
formalization. -/
inductive CircleCircleNoMeetData (L M : EuclideanLollipop) : Type where
  | farApart :
      L.radius + M.radius <
        dist (toEuclideanR2 L.center) (toEuclideanR2 M.center) →
      CircleCircleNoMeetData L M
  | farApartSq :
      (L.radius + M.radius) ^ 2 < distSq2 L.center M.center →
      CircleCircleNoMeetData L M
  | leftInside :
      dist (toEuclideanR2 L.center) (toEuclideanR2 M.center) + L.radius <
        M.radius →
      CircleCircleNoMeetData L M
  | rightInside :
      dist (toEuclideanR2 L.center) (toEuclideanR2 M.center) + M.radius <
        L.radius →
      CircleCircleNoMeetData L M
  | leftInsideSq :
      L.radius < M.radius →
      distSq2 L.center M.center < (M.radius - L.radius) ^ 2 →
      CircleCircleNoMeetData L M
  | rightInsideSq :
      M.radius < L.radius →
      distSq2 L.center M.center < (L.radius - M.radius) ^ 2 →
      CircleCircleNoMeetData L M

namespace CircleCircleNoMeetData

/-- A no-meet circle certificate proves that the lifted circle-circle component
is empty. -/
theorem empty {L M : EuclideanLollipop}
    (D : CircleCircleNoMeetData L M) :
    ∀ p : EuclideanR2, p ∉ euclideanCircleCircleSet L M := by
  cases D with
  | farApart hfar =>
      exact euclideanCircleCircleSet_empty_of_radius_add_lt_dist hfar
  | farApartSq hfar =>
      exact euclideanCircleCircleSet_empty_of_radius_add_sq_lt_distSq2 hfar
  | leftInside hcontained =>
      exact
        euclideanCircleCircleSet_empty_of_dist_add_left_radius_lt_right_radius
          hcontained
  | rightInside hcontained =>
      exact
        euclideanCircleCircleSet_empty_of_dist_add_right_radius_lt_left_radius
          hcontained
  | leftInsideSq hradius hcontained =>
      exact
        euclideanCircleCircleSet_empty_of_distSq2_lt_right_sub_left_radius_sq
          hradius hcontained
  | rightInsideSq hradius hcontained =>
      exact
        euclideanCircleCircleSet_empty_of_distSq2_lt_left_sub_right_radius_sq
          hradius hcontained

/-- A no-meet certificate is one formal branch of Paulsen's intriguing-circle
relation. -/
theorem circleIntriguingPair
    {L M : EuclideanLollipop}
    (D : CircleCircleNoMeetData L M) :
    TheoremOneEndToEnd.PaulsenLinearAlgebra.circleIntriguingPair
      L.radius M.radius L.center M.center := by
  unfold TheoremOneEndToEnd.PaulsenLinearAlgebra.circleIntriguingPair
    TheoremOneEndToEnd.PaulsenLinearAlgebra.circleObtuseCondition
  intro hobtuse
  cases D with
  | farApart hfar =>
      have hsum_nonneg : 0 ≤ L.radius + M.radius :=
        add_nonneg L.radius_pos.le M.radius_pos.le
      have hdist_nonneg :
          0 ≤ dist (toEuclideanR2 L.center) (toEuclideanR2 M.center) :=
        dist_nonneg
      have hfar_sq :
          (L.radius + M.radius) ^ 2 <
            dist (toEuclideanR2 L.center) (toEuclideanR2 M.center) ^ 2 :=
        (sq_lt_sq₀ hsum_nonneg hdist_nonneg).2 hfar
      have hdistSq :
          distSq2 L.center M.center =
            dist (toEuclideanR2 L.center) (toEuclideanR2 M.center) ^ 2 :=
        distSq2_eq_euclidean_dist_sq L.center M.center
      linarith
  | farApartSq hfar =>
      linarith
  | leftInside hcontained =>
      have hdiff_pos : 0 < M.radius - L.radius := by
        have hnonneg :
            0 ≤ dist (toEuclideanR2 L.center) (toEuclideanR2 M.center) :=
          dist_nonneg
        linarith
      have hdist :
          dist (toEuclideanR2 L.center) (toEuclideanR2 M.center) <
            M.radius - L.radius := by
        linarith
      have hdist_sq :
          dist (toEuclideanR2 L.center) (toEuclideanR2 M.center) ^ 2 <
            (M.radius - L.radius) ^ 2 :=
        (sq_lt_sq₀ dist_nonneg hdiff_pos.le).2 hdist
      have hdistSq :
          distSq2 L.center M.center =
            dist (toEuclideanR2 L.center) (toEuclideanR2 M.center) ^ 2 :=
        distSq2_eq_euclidean_dist_sq L.center M.center
      have hdiff_sq_lt :
          (M.radius - L.radius) ^ 2 < L.radius ^ 2 + M.radius ^ 2 := by
        nlinarith [L.radius_pos, M.radius_pos]
      linarith
  | rightInside hcontained =>
      have hdiff_pos : 0 < L.radius - M.radius := by
        have hnonneg :
            0 ≤ dist (toEuclideanR2 L.center) (toEuclideanR2 M.center) :=
          dist_nonneg
        linarith
      have hdist :
          dist (toEuclideanR2 L.center) (toEuclideanR2 M.center) <
            L.radius - M.radius := by
        linarith
      have hdist_sq :
          dist (toEuclideanR2 L.center) (toEuclideanR2 M.center) ^ 2 <
            (L.radius - M.radius) ^ 2 :=
        (sq_lt_sq₀ dist_nonneg hdiff_pos.le).2 hdist
      have hdistSq :
          distSq2 L.center M.center =
            dist (toEuclideanR2 L.center) (toEuclideanR2 M.center) ^ 2 :=
        distSq2_eq_euclidean_dist_sq L.center M.center
      have hdiff_sq_lt :
          (L.radius - M.radius) ^ 2 < L.radius ^ 2 + M.radius ^ 2 := by
        nlinarith [L.radius_pos, M.radius_pos]
      linarith
  | leftInsideSq _hradius hcontained =>
      have hdiff_sq_lt :
          (M.radius - L.radius) ^ 2 < L.radius ^ 2 + M.radius ^ 2 := by
        nlinarith [L.radius_pos, M.radius_pos]
      linarith
  | rightInsideSq _hradius hcontained =>
      have hdiff_sq_lt :
          (L.radius - M.radius) ^ 2 < L.radius ^ 2 + M.radius ^ 2 := by
        nlinarith [L.radius_pos, M.radius_pos]
      linarith

end CircleCircleNoMeetData

/-- The primitive carrier is exactly the preimage of the lifted Euclidean
carrier. -/
theorem carrier_eq_preimage_euclideanCarrier (L : EuclideanLollipop) :
    L.carrier = {p : R2 | toEuclideanR2 p ∈ euclideanCarrier L} := by
  ext p
  unfold EuclideanLollipop.carrier euclideanCarrier
  constructor
  · intro hp
    rcases hp with hcircle | hray
    · exact Or.inl
        ((mem_circleSet_iff_mem_euclideanSphere L.radius_pos.le).1 hcircle)
    · exact Or.inr
        ((mem_raySet_iff_mem_euclideanRaySet
          (p := p) (anchor := L.anchor) (direction := L.rayDirection)).1 hray)
  · intro hp
    rcases hp with hcircle | hray
    · exact Or.inl
        ((mem_circleSet_iff_mem_euclideanSphere L.radius_pos.le).2 hcircle)
    · exact Or.inr
        ((mem_raySet_iff_mem_euclideanRaySet
          (p := p) (anchor := L.anchor) (direction := L.rayDirection)).2 hray)

/-- Primitive carrier intersection is the preimage of the lifted carrier
intersection. -/
theorem pairIntersectionSet_eq_preimage_euclideanPairIntersectionSet
    (L M : EuclideanLollipop) :
    pairIntersectionSet L M =
      {p : R2 | toEuclideanR2 p ∈ euclideanPairIntersectionSet L M} := by
  ext p
  simp [pairIntersectionSet, euclideanPairIntersectionSet,
    carrier_eq_preimage_euclideanCarrier]

/-- A lifted carrier intersection splits into the four circle/ray component
types. -/
theorem mem_euclideanPairIntersectionSet_iff
    {L M : EuclideanLollipop} {p : EuclideanR2} :
    p ∈ euclideanPairIntersectionSet L M ↔
      p ∈ euclideanCircleCircleSet L M ∨
        p ∈ euclideanCircleRaySet L M ∨
          p ∈ euclideanRayCircleSet L M ∨
            p ∈ euclideanRayRaySet L M := by
  unfold euclideanPairIntersectionSet euclideanCarrier
    euclideanCircleCircleSet euclideanCircleRaySet
    euclideanRayCircleSet euclideanRayRaySet
  constructor
  · rintro ⟨hL, hM⟩
    rcases hL with hLcircle | hLray
    · rcases hM with hMcircle | hMray
      · exact Or.inl ⟨hLcircle, hMcircle⟩
      · exact Or.inr (Or.inl ⟨hLcircle, hMray⟩)
    · rcases hM with hMcircle | hMray
      · exact Or.inr (Or.inr (Or.inl ⟨hLray, hMcircle⟩))
      · exact Or.inr (Or.inr (Or.inr ⟨hLray, hMray⟩))
  · intro h
    rcases h with hcc | hcr | hrc | hrr
    · exact ⟨Or.inl hcc.1, Or.inl hcc.2⟩
    · exact ⟨Or.inl hcr.1, Or.inr hcr.2⟩
    · exact ⟨Or.inr hrc.1, Or.inl hrc.2⟩
    · exact ⟨Or.inr hrr.1, Or.inr hrr.2⟩

/-- Specialization of mathlib's two-sphere theorem: if two lifted primitive
circles are distinct and already have two distinct common points, then every
other common point is one of those two. -/
theorem eq_or_eq_of_mem_euclideanCircleCircleSet_of_two_witnesses
    {L M : EuclideanLollipop}
    (hLM :
      euclideanSphere L.center L.radius ≠ euclideanSphere M.center M.radius)
    {p₁ p₂ p : EuclideanR2}
    (hp₁₂ : p₁ ≠ p₂)
    (hp₁ : p₁ ∈ euclideanCircleCircleSet L M)
    (hp₂ : p₂ ∈ euclideanCircleCircleSet L M)
    (hp : p ∈ euclideanCircleCircleSet L M) :
    p = p₁ ∨ p = p₂ := by
  have hd : Module.finrank ℝ EuclideanR2 = 2 := by
    simp [EuclideanR2]
  exact
    EuclideanGeometry.eq_of_mem_sphere_of_mem_sphere_of_finrank_eq_two
      (V := EuclideanR2) (P := EuclideanR2)
      (s₁ := euclideanSphere L.center L.radius)
      (s₂ := euclideanSphere M.center M.radius)
      hd hLM hp₁₂ hp₁.1 hp₂.1 hp.1 hp₁.2 hp₂.2 hp.2

/-- Unlifted primitive-circle version of the two-circle bound. -/
theorem eq_or_eq_of_mem_circleSet_inter_of_two_witnesses
    {L M : EuclideanLollipop}
    (hLM :
      euclideanSphere L.center L.radius ≠ euclideanSphere M.center M.radius)
    {p₁ p₂ p : R2}
    (hp₁₂ : p₁ ≠ p₂)
    (hp₁ : p₁ ∈ circleSet L.center L.radius ∧
      p₁ ∈ circleSet M.center M.radius)
    (hp₂ : p₂ ∈ circleSet L.center L.radius ∧
      p₂ ∈ circleSet M.center M.radius)
    (hp : p ∈ circleSet L.center L.radius ∧
      p ∈ circleSet M.center M.radius) :
    p = p₁ ∨ p = p₂ := by
  have hp₁_lift : toEuclideanR2 p₁ ∈ euclideanCircleCircleSet L M := by
    exact ⟨
      (mem_circleSet_iff_mem_euclideanSphere L.radius_pos.le).1 hp₁.1,
      (mem_circleSet_iff_mem_euclideanSphere M.radius_pos.le).1 hp₁.2⟩
  have hp₂_lift : toEuclideanR2 p₂ ∈ euclideanCircleCircleSet L M := by
    exact ⟨
      (mem_circleSet_iff_mem_euclideanSphere L.radius_pos.le).1 hp₂.1,
      (mem_circleSet_iff_mem_euclideanSphere M.radius_pos.le).1 hp₂.2⟩
  have hp_lift : toEuclideanR2 p ∈ euclideanCircleCircleSet L M := by
    exact ⟨
      (mem_circleSet_iff_mem_euclideanSphere L.radius_pos.le).1 hp.1,
      (mem_circleSet_iff_mem_euclideanSphere M.radius_pos.le).1 hp.2⟩
  have hp₁₂_lift : toEuclideanR2 p₁ ≠ toEuclideanR2 p₂ := by
    intro h
    apply hp₁₂
    exact WithLp.toLp_injective 2 h
  rcases eq_or_eq_of_mem_euclideanCircleCircleSet_of_two_witnesses
      hLM hp₁₂_lift hp₁_lift hp₂_lift hp_lift with h | h
  · exact Or.inl (WithLp.toLp_injective 2 h)
  · exact Or.inr (WithLp.toLp_injective 2 h)

/-- The lifted anchor lies on the lifted mathlib sphere. -/
theorem anchor_mem_euclideanSphere (L : EuclideanLollipop) :
    toEuclideanR2 L.anchor ∈ euclideanSphere L.center L.radius := by
  exact (mem_circleSet_iff_mem_euclideanSphere L.radius_pos.le).1
    L.anchor_on_circle

/-- A lifted ray point lies on the affine line through the anchor in the ray
direction. -/
theorem mem_anchor_line_of_mem_euclideanRaySet
    (L : EuclideanLollipop) {p : EuclideanR2}
    (hp : p ∈ euclideanRaySet L.anchor L.rayDirection) :
    p ∈ AffineSubspace.mk' (toEuclideanR2 L.anchor)
      (ℝ ∙ toEuclideanR2 L.rayDirection) := by
  rcases hp with ⟨t, _ht, rfl⟩
  rw [AffineSubspace.mem_mk']
  simpa using
    Submodule.smul_mem (ℝ ∙ toEuclideanR2 L.rayDirection) t
      (Submodule.mem_span_singleton_self (toEuclideanR2 L.rayDirection))

/-- A lifted ray point lies on the named supporting affine line of the ray. -/
theorem mem_euclideanRayLine_of_mem_euclideanRaySet
    (L : EuclideanLollipop) {p : EuclideanR2}
    (hp : p ∈ euclideanRaySet L.anchor L.rayDirection) :
    p ∈ euclideanRayLine L := by
  rw [euclideanRayLine_eq_mk']
  exact mem_anchor_line_of_mem_euclideanRaySet L hp

/-- A point in a ray-circle component lies on the affine line of the ray. -/
theorem mem_anchor_line_of_mem_euclideanRayCircleSet
    {L M : EuclideanLollipop} {p : EuclideanR2}
    (hp : p ∈ euclideanRayCircleSet L M) :
    p ∈ AffineSubspace.mk' (toEuclideanR2 L.anchor)
      (ℝ ∙ toEuclideanR2 L.rayDirection) :=
  mem_anchor_line_of_mem_euclideanRaySet L hp.1

/-- A point in a circle-ray component lies on the affine line of the ray. -/
theorem mem_anchor_line_of_mem_euclideanCircleRaySet
    {L M : EuclideanLollipop} {p : EuclideanR2}
    (hp : p ∈ euclideanCircleRaySet L M) :
    p ∈ AffineSubspace.mk' (toEuclideanR2 M.anchor)
      (ℝ ∙ toEuclideanR2 M.rayDirection) :=
  mem_anchor_line_of_mem_euclideanRaySet M hp.2

/-- A point in a ray-circle component lies on the named supporting line of
the ray. -/
theorem mem_euclideanRayLine_of_mem_euclideanRayCircleSet
    {L M : EuclideanLollipop} {p : EuclideanR2}
    (hp : p ∈ euclideanRayCircleSet L M) :
    p ∈ euclideanRayLine L :=
  mem_euclideanRayLine_of_mem_euclideanRaySet L hp.1

/-- A point in a circle-ray component lies on the named supporting line of
the ray. -/
theorem mem_euclideanRayLine_of_mem_euclideanCircleRaySet
    {L M : EuclideanLollipop} {p : EuclideanR2}
    (hp : p ∈ euclideanCircleRaySet L M) :
    p ∈ euclideanRayLine M :=
  mem_euclideanRayLine_of_mem_euclideanRaySet M hp.2

/-- Orthogonal projection of a point to a lollipop ray's supporting line.  The
supporting line is nonempty because it contains the ray anchor. -/
noncomputable def euclideanRayLineProjection
    (L : EuclideanLollipop) (p : EuclideanR2) : EuclideanR2 :=
  letI : Nonempty (euclideanRayLine L) :=
    ⟨⟨toEuclideanR2 L.anchor, anchor_mem_euclideanRayLine L⟩⟩
  EuclideanGeometry.orthogonalProjection (euclideanRayLine L) p

/-- The projection helper realizes the metric distance to the supporting line
as `Metric.infDist`. -/
theorem dist_euclideanRayLineProjection_eq_infDist
    (L : EuclideanLollipop) (p : EuclideanR2) :
    dist p (euclideanRayLineProjection L p) =
      Metric.infDist p (euclideanRayLine L : Set EuclideanR2) := by
  unfold euclideanRayLineProjection
  letI : Nonempty (euclideanRayLine L) :=
    ⟨⟨toEuclideanR2 L.anchor, anchor_mem_euclideanRayLine L⟩⟩
  exact EuclideanGeometry.dist_orthogonalProjection_eq_infDist
    (euclideanRayLine L) p

/-- If the center of a circle is farther from a ray's supporting line than the
circle radius, then the circle-ray component is empty.  This is a convenient
mathlib projection/`infDist` certificate for one common close/intriguing
savings branch. -/
theorem euclideanCircleRaySet_empty_of_radius_lt_infDist_rayLine
    {L M : EuclideanLollipop}
    (hsep :
      L.radius <
        Metric.infDist (toEuclideanR2 L.center)
          (euclideanRayLine M : Set EuclideanR2)) :
    ∀ p : EuclideanR2, p ∉ euclideanCircleRaySet L M := by
  intro p hp
  have hp_line : p ∈ (euclideanRayLine M : Set EuclideanR2) :=
    mem_euclideanRayLine_of_mem_euclideanCircleRaySet hp
  have hp_sphere :
      dist p (toEuclideanR2 L.center) = L.radius :=
    EuclideanGeometry.mem_sphere.1 hp.1
  have hle :
      Metric.infDist (toEuclideanR2 L.center)
          (euclideanRayLine M : Set EuclideanR2) ≤
        dist (toEuclideanR2 L.center) p :=
    Metric.infDist_le_dist_of_mem hp_line
  rw [dist_comm (toEuclideanR2 L.center) p, hp_sphere] at hle
  linarith

/-- Symmetric line-distance certificate for an empty ray-circle component. -/
theorem euclideanRayCircleSet_empty_of_radius_lt_infDist_rayLine
    {L M : EuclideanLollipop}
    (hsep :
      M.radius <
        Metric.infDist (toEuclideanR2 M.center)
          (euclideanRayLine L : Set EuclideanR2)) :
    ∀ p : EuclideanR2, p ∉ euclideanRayCircleSet L M := by
  intro p hp
  have hp_line : p ∈ (euclideanRayLine L : Set EuclideanR2) :=
    mem_euclideanRayLine_of_mem_euclideanRayCircleSet hp
  have hp_sphere :
      dist p (toEuclideanR2 M.center) = M.radius :=
    EuclideanGeometry.mem_sphere.1 hp.2
  have hle :
      Metric.infDist (toEuclideanR2 M.center)
          (euclideanRayLine L : Set EuclideanR2) ≤
        dist (toEuclideanR2 M.center) p :=
    Metric.infDist_le_dist_of_mem hp_line
  rw [dist_comm (toEuclideanR2 M.center) p, hp_sphere] at hle
  linarith

/-- Coordinate determinant criterion for an empty circle-ray component.  If
the squared perpendicular determinant from the circle center to the ray's
supporting line is larger than `radius^2 * |direction|^2`, then the line, and
hence the ray, misses the circle. -/
theorem euclideanCircleRaySet_empty_of_radius_sq_mul_normSq2_lt_det2_sq
    {L M : EuclideanLollipop}
    (hsep :
      L.radius ^ 2 * normSq2 M.rayDirection <
        det2 (M.anchor - L.center) M.rayDirection ^ 2) :
    ∀ p : EuclideanR2, p ∉ euclideanCircleRaySet L M := by
  intro p hp
  rcases hp.2 with ⟨t, _ht, hp_eq⟩
  let x : R2 := M.anchor + t • M.rayDirection
  have hx_det :
      det2 (x - L.center) M.rayDirection =
        det2 (M.anchor - L.center) M.rayDirection := by
    simpa [x] using
      det2_line_vadd_sub_right M.anchor L.center M.rayDirection t
  have hx_dist :
      distSq2 x L.center = L.radius ^ 2 := by
    have hp_sphere :
        dist p (toEuclideanR2 L.center) = L.radius :=
      EuclideanGeometry.mem_sphere.1 hp.1
    have hsq :
        dist p (toEuclideanR2 L.center) ^ 2 = L.radius ^ 2 := by
      rw [hp_sphere]
    have hp_to : p = toEuclideanR2 x := by
      simpa [x] using hp_eq
    have hsq' :
        dist (toEuclideanR2 x) (toEuclideanR2 L.center) ^ 2 =
          L.radius ^ 2 := by
      simpa [hp_to] using hsq
    simpa [distSq2_eq_euclidean_dist_sq] using hsq'.symm.symm
  have hdet_le :
      det2 (x - L.center) M.rayDirection ^ 2 ≤
        normSq2 (x - L.center) * normSq2 M.rayDirection :=
    det2_sq_le_normSq2_mul_normSq2 (x - L.center) M.rayDirection
  have hnorm :
      normSq2 (x - L.center) = L.radius ^ 2 := by
    simpa [distSq2] using hx_dist
  rw [hx_det, hnorm] at hdet_le
  exact (not_lt_of_ge hdet_le) hsep

/-- If a ray starts outside a circle and initially points weakly away from the
circle center, then the half-line ray misses the circle.  Unlike the
supporting-line separation certificate, this can apply when the full line
meets the circle behind the ray anchor. -/
theorem euclideanCircleRaySet_empty_of_radius_sq_lt_anchor_distSq2_of_dot_nonneg
    {L M : EuclideanLollipop}
    (hanchor : L.radius ^ 2 < distSq2 M.anchor L.center)
    (hdot : 0 ≤ dot2 (M.anchor - L.center) M.rayDirection) :
    ∀ p : EuclideanR2, p ∉ euclideanCircleRaySet L M := by
  intro p hp
  rcases hp.2 with ⟨t, ht, hp_eq⟩
  let x : R2 := M.anchor + t • M.rayDirection
  have hx_dist :
      distSq2 x L.center = L.radius ^ 2 := by
    have hp_sphere :
        dist p (toEuclideanR2 L.center) = L.radius :=
      EuclideanGeometry.mem_sphere.1 hp.1
    have hsq :
        dist p (toEuclideanR2 L.center) ^ 2 = L.radius ^ 2 := by
      rw [hp_sphere]
    have hp_to : p = toEuclideanR2 x := by
      simpa [x] using hp_eq
    have hsq' :
        dist (toEuclideanR2 x) (toEuclideanR2 L.center) ^ 2 =
          L.radius ^ 2 := by
      simpa [hp_to] using hsq
    simpa [distSq2_eq_euclidean_dist_sq] using hsq'.symm.symm
  have hnorm_nonneg : 0 ≤ normSq2 M.rayDirection := by
    unfold normSq2 dot2
    nlinarith [sq_nonneg (M.rayDirection 0),
      sq_nonneg (M.rayDirection 1)]
  have hmove_nonneg :
      0 ≤
        2 * t * dot2 (M.anchor - L.center) M.rayDirection +
          t ^ 2 * normSq2 M.rayDirection := by
    have hfirst :
        0 ≤ 2 * t * dot2 (M.anchor - L.center) M.rayDirection := by
      nlinarith
    have hsecond : 0 ≤ t ^ 2 * normSq2 M.rayDirection := by
      nlinarith [sq_nonneg t, hnorm_nonneg]
    nlinarith
  have hx_expand :=
    distSq2_vadd_smul_sub M.anchor L.center M.rayDirection t
  have hx_gt : L.radius ^ 2 < distSq2 x L.center := by
    rw [show x = M.anchor + t • M.rayDirection by rfl]
    rw [hx_expand]
    nlinarith
  rw [hx_dist] at hx_gt
  exact (lt_irrefl (L.radius ^ 2)) hx_gt

/-- Symmetric coordinate determinant criterion for an empty ray-circle
component. -/
theorem euclideanRayCircleSet_empty_of_radius_sq_mul_normSq2_lt_det2_sq
    {L M : EuclideanLollipop}
    (hsep :
      M.radius ^ 2 * normSq2 L.rayDirection <
        det2 (L.anchor - M.center) L.rayDirection ^ 2) :
    ∀ p : EuclideanR2, p ∉ euclideanRayCircleSet L M := by
  intro p hp
  rcases hp.1 with ⟨t, _ht, hp_eq⟩
  let x : R2 := L.anchor + t • L.rayDirection
  have hx_det :
      det2 (x - M.center) L.rayDirection =
        det2 (L.anchor - M.center) L.rayDirection := by
    simpa [x] using
      det2_line_vadd_sub_right L.anchor M.center L.rayDirection t
  have hx_dist :
      distSq2 x M.center = M.radius ^ 2 := by
    have hp_sphere :
        dist p (toEuclideanR2 M.center) = M.radius :=
      EuclideanGeometry.mem_sphere.1 hp.2
    have hsq :
        dist p (toEuclideanR2 M.center) ^ 2 = M.radius ^ 2 := by
      rw [hp_sphere]
    have hp_to : p = toEuclideanR2 x := by
      simpa [x] using hp_eq
    have hsq' :
        dist (toEuclideanR2 x) (toEuclideanR2 M.center) ^ 2 =
          M.radius ^ 2 := by
      simpa [hp_to] using hsq
    simpa [distSq2_eq_euclidean_dist_sq] using hsq'.symm.symm
  have hdet_le :
      det2 (x - M.center) L.rayDirection ^ 2 ≤
        normSq2 (x - M.center) * normSq2 L.rayDirection :=
    det2_sq_le_normSq2_mul_normSq2 (x - M.center) L.rayDirection
  have hnorm :
      normSq2 (x - M.center) = M.radius ^ 2 := by
    simpa [distSq2] using hx_dist
  rw [hx_det, hnorm] at hdet_le
  exact (not_lt_of_ge hdet_le) hsep

/-- Symmetric half-line criterion for an empty ray-circle component. -/
theorem euclideanRayCircleSet_empty_of_radius_sq_lt_anchor_distSq2_of_dot_nonneg
    {L M : EuclideanLollipop}
    (hanchor : M.radius ^ 2 < distSq2 L.anchor M.center)
    (hdot : 0 ≤ dot2 (L.anchor - M.center) L.rayDirection) :
    ∀ p : EuclideanR2, p ∉ euclideanRayCircleSet L M := by
  intro p hp
  rcases hp.1 with ⟨t, ht, hp_eq⟩
  let x : R2 := L.anchor + t • L.rayDirection
  have hx_dist :
      distSq2 x M.center = M.radius ^ 2 := by
    have hp_sphere :
        dist p (toEuclideanR2 M.center) = M.radius :=
      EuclideanGeometry.mem_sphere.1 hp.2
    have hsq :
        dist p (toEuclideanR2 M.center) ^ 2 = M.radius ^ 2 := by
      rw [hp_sphere]
    have hp_to : p = toEuclideanR2 x := by
      simpa [x] using hp_eq
    have hsq' :
        dist (toEuclideanR2 x) (toEuclideanR2 M.center) ^ 2 =
          M.radius ^ 2 := by
      simpa [hp_to] using hsq
    simpa [distSq2_eq_euclidean_dist_sq] using hsq'.symm.symm
  have hnorm_nonneg : 0 ≤ normSq2 L.rayDirection := by
    unfold normSq2 dot2
    nlinarith [sq_nonneg (L.rayDirection 0),
      sq_nonneg (L.rayDirection 1)]
  have hmove_nonneg :
      0 ≤
        2 * t * dot2 (L.anchor - M.center) L.rayDirection +
          t ^ 2 * normSq2 L.rayDirection := by
    have hfirst :
        0 ≤ 2 * t * dot2 (L.anchor - M.center) L.rayDirection := by
      nlinarith
    have hsecond : 0 ≤ t ^ 2 * normSq2 L.rayDirection := by
      nlinarith [sq_nonneg t, hnorm_nonneg]
    nlinarith
  have hx_expand :=
    distSq2_vadd_smul_sub L.anchor M.center L.rayDirection t
  have hx_gt : M.radius ^ 2 < distSq2 x M.center := by
    rw [show x = L.anchor + t • L.rayDirection by rfl]
    rw [hx_expand]
    nlinarith
  rw [hx_dist] at hx_gt
  exact (lt_irrefl (M.radius ^ 2)) hx_gt

/-- Coordinate criterion for an empty ray-ray component.  Parallel ray
directions whose supporting lines have nonzero offset determinant cannot
share a point. -/
theorem euclideanRayRaySet_empty_of_det2_directions_eq_zero_of_det2_anchor_sub_ne_zero
    {L M : EuclideanLollipop}
    (hparallel : det2 L.rayDirection M.rayDirection = 0)
    (hoffset : det2 (M.anchor - L.anchor) L.rayDirection ≠ 0) :
    ∀ p : EuclideanR2, p ∉ euclideanRayRaySet L M := by
  intro p hp
  rcases hp.1 with ⟨s, _hs, hpL⟩
  rcases hp.2 with ⟨t, _ht, hpM⟩
  rcases exists_smul_eq_of_det2_eq_zero_of_ne_zero
      L.rayDirection_ne_zero hparallel with ⟨c, hMdir⟩
  have hpoints :
      L.anchor + s • L.rayDirection =
        M.anchor + t • M.rayDirection := by
    apply toEuclideanR2_injective
    calc
      toEuclideanR2 (L.anchor + s • L.rayDirection)
          = toEuclideanR2 L.anchor + s • toEuclideanR2 L.rayDirection := by
            simp
      _ = p := hpL.symm
      _ = toEuclideanR2 M.anchor + t • toEuclideanR2 M.rayDirection := hpM
      _ = toEuclideanR2 (M.anchor + t • M.rayDirection) := by
            simp
  have hoffset_eq :
      M.anchor - L.anchor = (s - t * c) • L.rayDirection := by
    ext i
    have hi := congr_fun hpoints i
    simp [Pi.add_apply, Pi.sub_apply, Pi.smul_apply, hMdir] at hi ⊢
    linarith
  have hdet_zero :
      det2 (M.anchor - L.anchor) L.rayDirection = 0 := by
    rw [hoffset_eq]
    unfold det2
    simp [Pi.smul_apply]
    ring
  exact hoffset hdet_zero

/-- A concrete certificate that the circle of `L` does not meet the ray of
`M`, witnessed by separation from the ray's supporting line. -/
structure CircleRayNoMeetData (L M : EuclideanLollipop) : Type where
  radius_lt_infDist_rayLine :
    L.radius <
      Metric.infDist (toEuclideanR2 L.center)
        (euclideanRayLine M : Set EuclideanR2)

namespace CircleRayNoMeetData

/-- Projection-distance constructor for `CircleRayNoMeetData`, using
mathlib's theorem that the distance to the orthogonal projection is the
`Metric.infDist` to the affine subspace. -/
noncomputable def of_rayLineProjection
    {L M : EuclideanLollipop}
    (hsep :
      L.radius <
        dist (toEuclideanR2 L.center)
          (euclideanRayLineProjection M (toEuclideanR2 L.center))) :
    CircleRayNoMeetData L M where
  radius_lt_infDist_rayLine := by
    have hdist :
        dist (toEuclideanR2 L.center)
            (euclideanRayLineProjection M (toEuclideanR2 L.center)) =
          Metric.infDist (toEuclideanR2 L.center)
            (euclideanRayLine M : Set EuclideanR2) :=
      dist_euclideanRayLineProjection_eq_infDist M
        (toEuclideanR2 L.center)
    simpa [hdist] using hsep

/-- A circle-ray no-meet certificate proves that the lifted circle-ray
component is empty. -/
theorem empty {L M : EuclideanLollipop}
    (D : CircleRayNoMeetData L M) :
    ∀ p : EuclideanR2, p ∉ euclideanCircleRaySet L M :=
  euclideanCircleRaySet_empty_of_radius_lt_infDist_rayLine
    D.radius_lt_infDist_rayLine

end CircleRayNoMeetData

/-- A concrete certificate that the ray of `L` does not meet the circle of
`M`, witnessed by separation from the ray's supporting line. -/
structure RayCircleNoMeetData (L M : EuclideanLollipop) : Type where
  radius_lt_infDist_rayLine :
    M.radius <
      Metric.infDist (toEuclideanR2 M.center)
        (euclideanRayLine L : Set EuclideanR2)

namespace RayCircleNoMeetData

/-- Projection-distance constructor for `RayCircleNoMeetData`, using
mathlib's theorem that the distance to the orthogonal projection is the
`Metric.infDist` to the affine subspace. -/
noncomputable def of_rayLineProjection
    {L M : EuclideanLollipop}
    (hsep :
      M.radius <
        dist (toEuclideanR2 M.center)
          (euclideanRayLineProjection L (toEuclideanR2 M.center))) :
    RayCircleNoMeetData L M where
  radius_lt_infDist_rayLine := by
    have hdist :
        dist (toEuclideanR2 M.center)
            (euclideanRayLineProjection L (toEuclideanR2 M.center)) =
          Metric.infDist (toEuclideanR2 M.center)
            (euclideanRayLine L : Set EuclideanR2) :=
      dist_euclideanRayLineProjection_eq_infDist L
        (toEuclideanR2 M.center)
    simpa [hdist] using hsep

/-- A ray-circle no-meet certificate proves that the lifted ray-circle
component is empty. -/
theorem empty {L M : EuclideanLollipop}
    (D : RayCircleNoMeetData L M) :
    ∀ p : EuclideanR2, p ∉ euclideanRayCircleSet L M :=
  euclideanRayCircleSet_empty_of_radius_lt_infDist_rayLine
    D.radius_lt_infDist_rayLine

end RayCircleNoMeetData

/-- A point in a ray-ray component lies on the affine line of the first ray. -/
theorem mem_left_anchor_line_of_mem_euclideanRayRaySet
    {L M : EuclideanLollipop} {p : EuclideanR2}
    (hp : p ∈ euclideanRayRaySet L M) :
    p ∈ AffineSubspace.mk' (toEuclideanR2 L.anchor)
      (ℝ ∙ toEuclideanR2 L.rayDirection) :=
  mem_anchor_line_of_mem_euclideanRaySet L hp.1

/-- A point in a ray-ray component lies on the affine line of the second ray. -/
theorem mem_right_anchor_line_of_mem_euclideanRayRaySet
    {L M : EuclideanLollipop} {p : EuclideanR2}
    (hp : p ∈ euclideanRayRaySet L M) :
    p ∈ AffineSubspace.mk' (toEuclideanR2 M.anchor)
      (ℝ ∙ toEuclideanR2 M.rayDirection) :=
  mem_anchor_line_of_mem_euclideanRaySet M hp.2

/-- A point in a ray-ray component lies on the named supporting line of the
first ray. -/
theorem mem_left_euclideanRayLine_of_mem_euclideanRayRaySet
    {L M : EuclideanLollipop} {p : EuclideanR2}
    (hp : p ∈ euclideanRayRaySet L M) :
    p ∈ euclideanRayLine L :=
  mem_euclideanRayLine_of_mem_euclideanRaySet L hp.1

/-- A point in a ray-ray component lies on the named supporting line of the
second ray. -/
theorem mem_right_euclideanRayLine_of_mem_euclideanRayRaySet
    {L M : EuclideanLollipop} {p : EuclideanR2}
    (hp : p ∈ euclideanRayRaySet L M) :
    p ∈ euclideanRayLine M :=
  mem_euclideanRayLine_of_mem_euclideanRaySet M hp.2

/-- If the two supporting ray lines are disjoint as sets, then the actual
ray-ray component is empty. -/
theorem euclideanRayRaySet_empty_of_rayLine_disjoint
    {L M : EuclideanLollipop}
    (hdisj :
      Disjoint (euclideanRayLine L : Set EuclideanR2)
        (euclideanRayLine M : Set EuclideanR2)) :
    ∀ p : EuclideanR2, p ∉ euclideanRayRaySet L M := by
  intro p hp
  have hpL : p ∈ (euclideanRayLine L : Set EuclideanR2) :=
    mem_left_euclideanRayLine_of_mem_euclideanRayRaySet hp
  have hpM : p ∈ (euclideanRayLine M : Set EuclideanR2) :=
    mem_right_euclideanRayLine_of_mem_euclideanRayRaySet hp
  exact (Set.disjoint_left.1 hdisj hpL) hpM

/-- A concrete certificate that the two ray components do not meet, witnessed
by disjoint supporting lines. -/
structure RayRayNoMeetData (L M : EuclideanLollipop) : Type where
  rayLine_disjoint :
    Disjoint (euclideanRayLine L : Set EuclideanR2)
      (euclideanRayLine M : Set EuclideanR2)

namespace RayRayNoMeetData

/-- A ray-ray no-meet certificate proves that the lifted ray-ray component is
empty. -/
theorem empty {L M : EuclideanLollipop}
    (D : RayRayNoMeetData L M) :
    ∀ p : EuclideanR2, p ∉ euclideanRayRaySet L M :=
  euclideanRayRaySet_empty_of_rayLine_disjoint D.rayLine_disjoint

end RayRayNoMeetData

/-- Two distinct common points of two ray supporting lines force the two
supporting lines to be equal. -/
theorem euclideanRayLine_eq_of_two_common_points
    {L M : EuclideanLollipop} {p₁ p₂ : EuclideanR2}
    (hp₁₂ : p₁ ≠ p₂)
    (hp₁L : p₁ ∈ euclideanRayLine L)
    (hp₂L : p₂ ∈ euclideanRayLine L)
    (hp₁M : p₁ ∈ euclideanRayLine M)
    (hp₂M : p₂ ∈ euclideanRayLine M) :
    euclideanRayLine L = euclideanRayLine M := by
  have hL : line[ℝ, p₁, p₂] = euclideanRayLine L :=
    affineSpan_pair_eq_of_mem_of_mem_of_ne hp₁L hp₂L hp₁₂
  have hM : line[ℝ, p₁, p₂] = euclideanRayLine M :=
    affineSpan_pair_eq_of_mem_of_mem_of_ne hp₁M hp₂M hp₁₂
  exact hL.symm.trans hM

/-- Two distinct points in a ray-ray component force equality of the two
supporting ray lines. -/
theorem euclideanRayLine_eq_of_two_mem_euclideanRayRaySet
    {L M : EuclideanLollipop} {p₁ p₂ : EuclideanR2}
    (hp₁₂ : p₁ ≠ p₂)
    (hp₁ : p₁ ∈ euclideanRayRaySet L M)
    (hp₂ : p₂ ∈ euclideanRayRaySet L M) :
    euclideanRayLine L = euclideanRayLine M := by
  exact euclideanRayLine_eq_of_two_common_points hp₁₂
    (mem_left_euclideanRayLine_of_mem_euclideanRayRaySet hp₁)
    (mem_left_euclideanRayLine_of_mem_euclideanRayRaySet hp₂)
    (mem_right_euclideanRayLine_of_mem_euclideanRayRaySet hp₁)
    (mem_right_euclideanRayLine_of_mem_euclideanRayRaySet hp₂)

/-- If two ray supporting lines are different, their lifted ray-ray component
contains at most one point. -/
theorem eq_of_mem_euclideanRayRaySet_of_rayLine_ne
    {L M : EuclideanLollipop}
    (hline : euclideanRayLine L ≠ euclideanRayLine M)
    {p₁ p₂ : EuclideanR2}
    (hp₁ : p₁ ∈ euclideanRayRaySet L M)
    (hp₂ : p₂ ∈ euclideanRayRaySet L M) :
    p₁ = p₂ := by
  by_contra hp₁₂
  exact hline
    (euclideanRayLine_eq_of_two_mem_euclideanRayRaySet hp₁₂ hp₁ hp₂)

/-- Set-level version: noncoincident ray supporting lines have a subsingleton
ray-ray component. -/
theorem euclideanRayRaySet_subsingleton_of_rayLine_ne
    {L M : EuclideanLollipop}
    (hline : euclideanRayLine L ≠ euclideanRayLine M) :
    (euclideanRayRaySet L M).Subsingleton := by
  intro p₁ hp₁ p₂ hp₂
  exact eq_of_mem_euclideanRayRaySet_of_rayLine_ne hline hp₁ hp₂

/-- A ray supporting line and a Euclidean sphere have at most two common
points once two distinct common points have been named. -/
theorem eq_or_eq_of_mem_euclideanSphere_of_mem_euclideanRayLine_of_two_witnesses
    {s : EuclideanGeometry.Sphere EuclideanR2}
    {L : EuclideanLollipop}
    {p₁ p₂ p : EuclideanR2}
    (hp₁₂ : p₁ ≠ p₂)
    (hp₁_sphere : p₁ ∈ s)
    (hp₂_sphere : p₂ ∈ s)
    (hp_sphere : p ∈ s)
    (hp₁_line : p₁ ∈ euclideanRayLine L)
    (hp₂_line : p₂ ∈ euclideanRayLine L)
    (hp_line : p ∈ euclideanRayLine L) :
    p = p₁ ∨ p = p₂ := by
  have hline : line[ℝ, p₁, p₂] = euclideanRayLine L :=
    affineSpan_pair_eq_of_mem_of_mem_of_ne hp₁_line hp₂_line hp₁₂
  have hp_line_pair : p ∈ line[ℝ, p₁, p₂] := by
    rwa [hline]
  have hp₂_cases :
      p₂ = p₁ ∨ p₂ = s.secondInter p₁ (p₂ -ᵥ p₁) := by
    exact
      ((s.eq_or_eq_secondInter_iff_mem_of_mem_affineSpan_pair
        hp₁_sphere (right_mem_affineSpan_pair ℝ p₁ p₂)).2 hp₂_sphere)
  have hsecond : s.secondInter p₁ (p₂ -ᵥ p₁) = p₂ := by
    rcases hp₂_cases with hp₂_eq | hp₂_eq
    · exact False.elim (hp₁₂ hp₂_eq.symm)
    · exact hp₂_eq.symm
  have hp_cases : p = p₁ ∨ p = s.secondInter p₁ (p₂ -ᵥ p₁) := by
    exact
      ((s.eq_or_eq_secondInter_iff_mem_of_mem_affineSpan_pair
        hp₁_sphere hp_line_pair).2 hp_sphere)
  rcases hp_cases with hp_eq | hp_eq
  · exact Or.inl hp_eq
  · exact Or.inr (hp_eq.trans hsecond)

/-- A circle-ray component has at most two points once two distinct component
points have been named. -/
theorem eq_or_eq_of_mem_euclideanCircleRaySet_of_two_witnesses
    {L M : EuclideanLollipop} {p₁ p₂ p : EuclideanR2}
    (hp₁₂ : p₁ ≠ p₂)
    (hp₁ : p₁ ∈ euclideanCircleRaySet L M)
    (hp₂ : p₂ ∈ euclideanCircleRaySet L M)
    (hp : p ∈ euclideanCircleRaySet L M) :
    p = p₁ ∨ p = p₂ := by
  exact eq_or_eq_of_mem_euclideanSphere_of_mem_euclideanRayLine_of_two_witnesses
    (s := euclideanSphere L.center L.radius)
    (L := M) hp₁₂
    hp₁.1 hp₂.1 hp.1
    (mem_euclideanRayLine_of_mem_euclideanCircleRaySet hp₁)
    (mem_euclideanRayLine_of_mem_euclideanCircleRaySet hp₂)
    (mem_euclideanRayLine_of_mem_euclideanCircleRaySet hp)

/-- A ray-circle component has at most two points once two distinct component
points have been named. -/
theorem eq_or_eq_of_mem_euclideanRayCircleSet_of_two_witnesses
    {L M : EuclideanLollipop} {p₁ p₂ p : EuclideanR2}
    (hp₁₂ : p₁ ≠ p₂)
    (hp₁ : p₁ ∈ euclideanRayCircleSet L M)
    (hp₂ : p₂ ∈ euclideanRayCircleSet L M)
    (hp : p ∈ euclideanRayCircleSet L M) :
    p = p₁ ∨ p = p₂ := by
  exact eq_or_eq_of_mem_euclideanSphere_of_mem_euclideanRayLine_of_two_witnesses
    (s := euclideanSphere M.center M.radius)
    (L := L) hp₁₂
    hp₁.2 hp₂.2 hp.2
    (mem_euclideanRayLine_of_mem_euclideanRayCircleSet hp₁)
    (mem_euclideanRayLine_of_mem_euclideanRayCircleSet hp₂)
    (mem_euclideanRayLine_of_mem_euclideanRayCircleSet hp)

/-- A point on a line through the lifted anchor lies on the lifted circle
exactly when it is the anchor or mathlib's second line/sphere intersection.
This is the standard mathlib theorem needed for future circle-ray intersection
counts. -/
theorem eq_or_eq_secondInter_of_mem_anchor_line_iff_mem_euclideanSphere
    (L : EuclideanLollipop) {p : EuclideanR2}
    (hp_line :
      p ∈ AffineSubspace.mk' (toEuclideanR2 L.anchor)
        (ℝ ∙ toEuclideanR2 L.rayDirection)) :
    p = toEuclideanR2 L.anchor ∨
        p = (euclideanSphere L.center L.radius).secondInter
          (toEuclideanR2 L.anchor) (toEuclideanR2 L.rayDirection) ↔
      p ∈ euclideanSphere L.center L.radius := by
  exact
    (euclideanSphere L.center L.radius).eq_or_eq_secondInter_of_mem_mk'_span_singleton_iff_mem
      (anchor_mem_euclideanSphere L) hp_line

/-- Any lifted point lying both on a lollipop ray and on its circle is either
the anchor or mathlib's second intersection of that line with the circle. -/
theorem eq_or_eq_secondInter_of_mem_euclideanRaySet_of_mem_euclideanSphere
    (L : EuclideanLollipop) {p : EuclideanR2}
    (hp_ray : p ∈ euclideanRaySet L.anchor L.rayDirection)
    (hp_sphere : p ∈ euclideanSphere L.center L.radius) :
    p = toEuclideanR2 L.anchor ∨
      p = (euclideanSphere L.center L.radius).secondInter
        (toEuclideanR2 L.anchor) (toEuclideanR2 L.rayDirection) := by
  exact
    ((eq_or_eq_secondInter_of_mem_anchor_line_iff_mem_euclideanSphere
      L (mem_anchor_line_of_mem_euclideanRaySet L hp_ray)).2 hp_sphere)

end PrimitiveGeometry
end TheoremOneManuscript
end Lollipop
