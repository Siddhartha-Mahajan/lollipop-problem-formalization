import Lollipop.Concrete.Topology
import Lollipop.Internal.ColoredTuran.GeometricPaulsenReduction
import Lollipop.Internal.Manuscript.PrimitiveGeometry.NormalizedBearing
import Lollipop.Internal.Manuscript.PrimitiveGeometry.SphereBridge
import Mathlib.Analysis.SpecialFunctions.Complex.Arg
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Tactic

/-!
# Coordinates and normalized bearings for concrete lollipops

The old combinatorial backend expects centers in `Fin 2 → ℝ`, radii, and one
normalized angle in `[0,1)`.  This file derives all of them from the concrete
`center/radial` model.  In particular, the angle is not an independent field.
-/

noncomputable section

namespace Lollipop
namespace Concrete
namespace EndToEnd

open Set

abbrev R2 := TheoremOneEndToEnd.PaulsenLinearAlgebra.R2

namespace R2

def ofPoint (p : Point) : R2 := fun i => p i

def toPoint (p : R2) : Point :=
  TheoremOneManuscript.PrimitiveGeometry.toEuclideanR2 p

@[simp] theorem ofPoint_apply (p : Point) (i : Fin 2) : ofPoint p i = p i := rfl
@[simp] theorem toPoint_apply (p : R2) (i : Fin 2) : toPoint p i = p i :=
  TheoremOneManuscript.PrimitiveGeometry.toEuclideanR2_apply p i

@[simp] theorem ofPoint_toPoint (p : R2) : ofPoint (toPoint p) = p := by
  ext i
  exact toPoint_apply p i

@[simp] theorem toPoint_ofPoint (p : Point) : toPoint (ofPoint p) = p := by
  ext i
  exact toPoint_apply (ofPoint p) i

@[simp] theorem ofPoint_add (x y : Point) :
    ofPoint (x + y) = ofPoint x + ofPoint y := by ext i; rfl

@[simp] theorem ofPoint_sub (x y : Point) :
    ofPoint (x - y) = ofPoint x - ofPoint y := by ext i; rfl

@[simp] theorem ofPoint_smul (a : ℝ) (x : Point) :
    ofPoint (a • x) = a • ofPoint x := by ext i; rfl

@[simp] theorem toPoint_add (x y : R2) :
    toPoint (x + y) = toPoint x + toPoint y :=
  TheoremOneManuscript.PrimitiveGeometry.toEuclideanR2_add x y

@[simp] theorem toPoint_sub (x y : R2) :
    toPoint (x - y) = toPoint x - toPoint y :=
  TheoremOneManuscript.PrimitiveGeometry.toEuclideanR2_sub x y

@[simp] theorem toPoint_smul (a : ℝ) (x : R2) :
    toPoint (a • x) = a • toPoint x :=
  TheoremOneManuscript.PrimitiveGeometry.toEuclideanR2_smul a x

/-- Squared norm in the two coordinate models. -/
theorem norm_sq_toPoint (x : R2) :
    ‖toPoint x‖ ^ 2 =
      TheoremOneEndToEnd.PaulsenLinearAlgebra.normSq2 x := by
  calc
    ‖toPoint x‖ ^ 2 = dist (toPoint x) (toPoint 0) ^ 2 := by
      rw [show toPoint 0 = (0 : Point) by ext i; simp [toPoint]]
      rw [dist_zero_right]
    _ = TheoremOneEndToEnd.PaulsenLinearAlgebra.distSq2 x 0 := by
      simpa [toPoint] using
        (TheoremOneManuscript.PrimitiveGeometry.distSq2_eq_euclidean_dist_sq x 0).symm
    _ = TheoremOneEndToEnd.PaulsenLinearAlgebra.normSq2 x := by
      simp [TheoremOneEndToEnd.PaulsenLinearAlgebra.distSq2]

end R2

/-- Polar-coordinate existence in normalized-turn form.

This is the only trigonometric API port in the coordinate layer.  The proof uses
the complex argument, adds one full turn when negative, and divides by `2π`. -/
theorem exists_normalized_angle
    (u : R2)
    (hu : TheoremOneEndToEnd.PaulsenLinearAlgebra.normSq2 u = 1) :
    ∃ θ : ℝ,
      0 ≤ θ ∧ θ < 1 ∧
      u = TheoremOneManuscript.PrimitiveGeometry.angleDirection
        (2 * Real.pi * θ) := by
  have hxy : (u 0) ^ 2 + (u 1) ^ 2 = 1 := by
    unfold TheoremOneEndToEnd.PaulsenLinearAlgebra.normSq2
      TheoremOneEndToEnd.PaulsenLinearAlgebra.dot2 at hu
    nlinarith
  have hne : u 0 ≠ 0 ∨ u 1 ≠ 0 := by
    by_contra h
    push Not at h
    nlinarith
  let z : ℂ := (u 0 : ℂ) + (u 1 : ℂ) * Complex.I
  have hnormSq : Complex.normSq z = 1 := by
    simpa [z, Complex.normSq_add_mul_I] using hxy
  have hnormSq' : ‖z‖ ^ 2 = 1 := by
    rw [← Complex.normSq_eq_norm_sq, hnormSq]
  have hnorm : ‖z‖ = 1 := by
    nlinarith [norm_nonneg z, hnormSq']
  have hz : z ≠ 0 := by
    intro hz0
    have : ‖z‖ = 0 := by simpa [hz0]
    linarith
  let φ : ℝ := Complex.arg z
  have hcos : Real.cos φ = u 0 := by
    have := Complex.norm_mul_cos_arg z
    simpa [φ, z, hnorm] using this
  have hsin : Real.sin φ = u 1 := by
    have := Complex.norm_mul_sin_arg z
    simpa [φ, z, hnorm] using this
  have hlo : -Real.pi < φ := by
    simpa [φ] using Complex.neg_pi_lt_arg z
  have hhi : φ ≤ Real.pi := by
    simpa [φ] using Complex.arg_le_pi z
  by_cases hφ : φ < 0
  · refine ⟨(φ + 2 * Real.pi) / (2 * Real.pi), ?_, ?_, ?_⟩
    · exact div_nonneg (by nlinarith [Real.pi_pos, hlo]) Real.two_pi_pos.le
    · apply (div_lt_one (by positivity : 0 < 2 * Real.pi)).2
      nlinarith [Real.pi_pos]
    · ext i
      have hangle :
          2 * Real.pi * ((φ + 2 * Real.pi) / (2 * Real.pi)) =
            φ + 2 * Real.pi := by
        field_simp [mul_ne_zero two_ne_zero Real.pi_ne_zero]
      fin_cases i
      · simp [hangle, TheoremOneManuscript.PrimitiveGeometry.angleDirection,
          TheoremOneManuscript.PrimitiveGeometry.point2,
          Real.cos_add_two_pi, hcos]
      · simp [hangle, TheoremOneManuscript.PrimitiveGeometry.angleDirection,
          TheoremOneManuscript.PrimitiveGeometry.point2,
          Real.sin_add_two_pi, hsin]
  · have hφ0 : 0 ≤ φ := le_of_not_gt hφ
    refine ⟨φ / (2 * Real.pi), div_nonneg hφ0 (by positivity), ?_, ?_⟩
    · apply (div_lt_one (by positivity : 0 < 2 * Real.pi)).2
      nlinarith [Real.pi_pos]
    · ext i
      have hangle :
          2 * Real.pi * (φ / (2 * Real.pi)) = φ := by
        field_simp [mul_ne_zero two_ne_zero Real.pi_ne_zero]
      fin_cases i
      · simpa [hangle, TheoremOneManuscript.PrimitiveGeometry.angleDirection,
          TheoremOneManuscript.PrimitiveGeometry.point2] using hcos.symm
      · simpa [hangle, TheoremOneManuscript.PrimitiveGeometry.angleDirection,
          TheoremOneManuscript.PrimitiveGeometry.point2] using hsin.symm

/-- A normalized angle chosen from the actual unit radial direction. -/
def normalizedDirection (L : Lollipop) : ℝ :=
  Classical.choose (exists_normalized_angle (R2.ofPoint L.unitRadial) (by
    rw [← R2.norm_sq_toPoint]
    simp))

@[simp] theorem normalizedDirection_nonneg (L : Lollipop) :
    0 ≤ normalizedDirection L :=
  (Classical.choose_spec
    (exists_normalized_angle (R2.ofPoint L.unitRadial) (by
      rw [← R2.norm_sq_toPoint]; simp))).1

@[simp] theorem normalizedDirection_lt_one (L : Lollipop) :
    normalizedDirection L < 1 :=
  (Classical.choose_spec
    (exists_normalized_angle (R2.ofPoint L.unitRadial) (by
      rw [← R2.norm_sq_toPoint]; simp))).2.1

@[simp] theorem unitRadial_bearing (L : Lollipop) :
    R2.ofPoint L.unitRadial =
      TheoremOneManuscript.PrimitiveGeometry.angleDirection
        (2 * Real.pi * normalizedDirection L) :=
  (Classical.choose_spec
    (exists_normalized_angle (R2.ofPoint L.unitRadial) (by
      rw [← R2.norm_sq_toPoint]; simp))).2.2

/-- Concrete lollipop viewed by the existing primitive-coordinate library. -/
def toPrimitive (L : Lollipop) :
    TheoremOneManuscript.PrimitiveGeometry.EuclideanLollipop where
  center := R2.ofPoint L.center
  radius := L.radius
  radius_pos := L.radius_pos
  anchor := R2.ofPoint L.anchor
  rayDirection := R2.ofPoint L.unitRadial
  rayDirection_ne_zero := by
    intro h
    have hpoint : L.unitRadial = 0 := by
      have hzero : R2.toPoint (0 : R2) = (0 : Point) := by
        ext i
        simp [R2.toPoint]
      exact (R2.toPoint_ofPoint L.unitRadial).symm.trans
        ((congrArg R2.toPoint h).trans hzero)
    have hnorm0 : ‖L.unitRadial‖ = 0 := by simp [hpoint]
    linarith [L.norm_unitRadial]
  anchor_on_circle := by
    unfold TheoremOneManuscript.PrimitiveGeometry.circleSet
    change TheoremOneEndToEnd.PaulsenLinearAlgebra.distSq2
        (R2.ofPoint L.anchor) (R2.ofPoint L.center) = L.radius ^ 2
    rw [TheoremOneManuscript.PrimitiveGeometry.distSq2_eq_euclidean_dist_sq]
    rw [show TheoremOneManuscript.PrimitiveGeometry.toEuclideanR2
          (R2.ofPoint L.anchor) = L.anchor by
        simpa [R2.toPoint] using R2.toPoint_ofPoint L.anchor]
    rw [show TheoremOneManuscript.PrimitiveGeometry.toEuclideanR2
          (R2.ofPoint L.center) = L.center by
        simpa [R2.toPoint] using R2.toPoint_ofPoint L.center]
    simp [Lollipop.anchor, Lollipop.radius, dist_eq_norm]
  normalizedDirection := normalizedDirection L
  normalizedDirection_nonneg := normalizedDirection_nonneg L
  normalizedDirection_lt_one := normalizedDirection_lt_one L

@[simp] theorem toPrimitive_hasNormalizedBearing (L : Lollipop) :
    (toPrimitive L).HasNormalizedBearing := by
  exact unitRadial_bearing L

/-- Coordinate maps consumed by the existing upper backend. -/
def centerR2 {n : ℕ} (A : Arrangement n) : Fin n → R2 :=
  fun i => R2.ofPoint (A i).center

def radiusR {n : ℕ} (A : Arrangement n) : Fin n → ℝ :=
  fun i => (A i).radius

def direction01 {n : ℕ} (A : Arrangement n) : Fin n → ℝ :=
  fun i => normalizedDirection (A i)

@[simp] theorem radiusR_pos {n : ℕ} (A : Arrangement n) :
    ∀ i, 0 < radiusR A i := fun i => (A i).radius_pos

@[simp] theorem direction01_nonneg {n : ℕ} (A : Arrangement n) :
    ∀ i, 0 ≤ direction01 A i := fun i => normalizedDirection_nonneg (A i)

@[simp] theorem direction01_lt_one {n : ℕ} (A : Arrangement n) :
    ∀ i, direction01 A i < 1 := fun i => normalizedDirection_lt_one (A i)

/-- Close normalized bearings imply a nonnegative dot product of actual stem
directions. -/
theorem radial_dot_nonneg_of_cyclicClose
    {L M : Lollipop}
    (hclose : TheoremOneEndToEnd.CloseDirection.cyclicClosePair
      (normalizedDirection L) (normalizedDirection M)) :
    0 ≤ TheoremOneEndToEnd.PaulsenLinearAlgebra.dot2
      (R2.ofPoint L.unitRadial) (R2.ofPoint M.unitRadial) := by
  exact TheoremOneManuscript.PrimitiveGeometry.EuclideanLollipop.dot2_rayDirection_nonneg_of_cyclicClosePair
      (toPrimitive_hasNormalizedBearing L)
      (toPrimitive_hasNormalizedBearing M) hclose

end EndToEnd
end Concrete
end Lollipop
