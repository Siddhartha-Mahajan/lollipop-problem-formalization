import Lollipop.Internal.Manuscript.PrimitiveGeometry.DirectionBridge

/-!
Compatibility between stored ray directions and normalized directions.

`EuclideanLollipop` deliberately keeps the actual ray vector and the
normalized angle used by the close-pair pigeonhole as separate fields.  This
file names the compatibility condition needed to use close-pair angle data in
coordinate route certificates.
-/

namespace Lollipop
namespace TheoremOneManuscript
namespace PrimitiveGeometry

open TheoremOneEndToEnd
open TheoremOneEndToEnd.PaulsenLinearAlgebra

/-- A lollipop's stored ray vector is the bearing vector determined by its
normalized direction. -/
def EuclideanLollipop.HasNormalizedBearing
    (L : EuclideanLollipop) : Prop :=
  L.rayDirection = angleDirection (2 * Real.pi * L.normalizedDirection)

namespace EuclideanLollipop

/-- Bearing vectors are unchanged after adding one full turn. -/
theorem angleDirection_add_two_pi (theta : ℝ) :
    angleDirection (theta + 2 * Real.pi) = angleDirection theta := by
  ext i; fin_cases i <;> simp [angleDirection, point2,
    Real.cos_add_two_pi, Real.sin_add_two_pi]

/-- Bearing vectors are unchanged after subtracting one full turn. -/
theorem angleDirection_sub_two_pi (theta : ℝ) :
    angleDirection (theta - 2 * Real.pi) = angleDirection theta := by
  ext i; fin_cases i <;> simp [angleDirection, point2,
    Real.cos_sub_two_pi, Real.sin_sub_two_pi]

/-- The `fromCenter` constructor has normalized-bearing compatibility when
its angle is exactly the normalized angle in radians. -/
theorem fromCenter_hasNormalizedBearing
    {center : R2} {radius theta normalizedDirection : ℝ}
    {hradius : 0 < radius}
    {hdir_nonneg : 0 ≤ normalizedDirection}
    {hdir_lt_one : normalizedDirection < 1}
    (htheta : theta = 2 * Real.pi * normalizedDirection) :
    (fromCenter center radius theta normalizedDirection
      hradius hdir_nonneg hdir_lt_one).HasNormalizedBearing := by
  simp [HasNormalizedBearing, fromCenter, htheta]

/-- The `fromCenter` constructor has normalized-bearing compatibility when
its angle differs from the normalized angle by one negative full turn. -/
theorem fromCenter_hasNormalizedBearing_of_eq_sub_two_pi
    {center : R2} {radius theta normalizedDirection : ℝ}
    {hradius : 0 < radius}
    {hdir_nonneg : 0 ≤ normalizedDirection}
    {hdir_lt_one : normalizedDirection < 1}
    (htheta : theta = 2 * Real.pi * normalizedDirection - 2 * Real.pi) :
    (fromCenter center radius theta normalizedDirection
      hradius hdir_nonneg hdir_lt_one).HasNormalizedBearing := by
  simp [HasNormalizedBearing, fromCenter, htheta, angleDirection_sub_two_pi]

/-- The `fromCenter` constructor has normalized-bearing compatibility when
its angle differs from the normalized angle by one positive full turn. -/
theorem fromCenter_hasNormalizedBearing_of_eq_add_two_pi
    {center : R2} {radius theta normalizedDirection : ℝ}
    {hradius : 0 < radius}
    {hdir_nonneg : 0 ≤ normalizedDirection}
    {hdir_lt_one : normalizedDirection < 1}
    (htheta : theta = 2 * Real.pi * normalizedDirection + 2 * Real.pi) :
    (fromCenter center radius theta normalizedDirection
      hradius hdir_nonneg hdir_lt_one).HasNormalizedBearing := by
  simp [HasNormalizedBearing, fromCenter, htheta, angleDirection_add_two_pi]

/-- The `fromAnchor` constructor has normalized-bearing compatibility when
its angle is exactly the normalized angle in radians. -/
theorem fromAnchor_hasNormalizedBearing
    {anchor : R2} {radius theta normalizedDirection : ℝ}
    {hradius : 0 < radius}
    {hdir_nonneg : 0 ≤ normalizedDirection}
    {hdir_lt_one : normalizedDirection < 1}
    (htheta : theta = 2 * Real.pi * normalizedDirection) :
    (fromAnchor anchor radius theta normalizedDirection
      hradius hdir_nonneg hdir_lt_one).HasNormalizedBearing := by
  simp [HasNormalizedBearing, fromAnchor, htheta]

/-- The `fromAnchor` constructor has normalized-bearing compatibility when
its angle differs from the normalized angle by one negative full turn. -/
theorem fromAnchor_hasNormalizedBearing_of_eq_sub_two_pi
    {anchor : R2} {radius theta normalizedDirection : ℝ}
    {hradius : 0 < radius}
    {hdir_nonneg : 0 ≤ normalizedDirection}
    {hdir_lt_one : normalizedDirection < 1}
    (htheta : theta = 2 * Real.pi * normalizedDirection - 2 * Real.pi) :
    (fromAnchor anchor radius theta normalizedDirection
      hradius hdir_nonneg hdir_lt_one).HasNormalizedBearing := by
  simp [HasNormalizedBearing, fromAnchor, htheta, angleDirection_sub_two_pi]

/-- The `fromAnchor` constructor has normalized-bearing compatibility when
its angle differs from the normalized angle by one positive full turn. -/
theorem fromAnchor_hasNormalizedBearing_of_eq_add_two_pi
    {anchor : R2} {radius theta normalizedDirection : ℝ}
    {hradius : 0 < radius}
    {hdir_nonneg : 0 ≤ normalizedDirection}
    {hdir_lt_one : normalizedDirection < 1}
    (htheta : theta = 2 * Real.pi * normalizedDirection + 2 * Real.pi) :
    (fromAnchor anchor radius theta normalizedDirection
      hradius hdir_nonneg hdir_lt_one).HasNormalizedBearing := by
  simp [HasNormalizedBearing, fromAnchor, htheta, angleDirection_add_two_pi]

/-- Under normalized-bearing compatibility, a cyclic-close pair has
nonnegative dot product between the actual stored ray directions. -/
theorem dot2_rayDirection_nonneg_of_cyclicClosePair
    {L M : EuclideanLollipop}
    (hL : L.HasNormalizedBearing)
    (hM : M.HasNormalizedBearing)
    (hclose :
      CloseDirection.cyclicClosePair L.normalizedDirection
        M.normalizedDirection) :
    0 ≤ dot2 L.rayDirection M.rayDirection := by
  rw [hL, hM]
  exact dot2_angleDirection_two_pi_nonneg_of_cyclicClosePair
    L.normalizedDirection_nonneg L.normalizedDirection_lt_one
    M.normalizedDirection_nonneg M.normalizedDirection_lt_one hclose

end EuclideanLollipop

namespace EuclideanLollipopArrangement

/-- Every lollipop in the arrangement has normalized-bearing compatibility. -/
def HasNormalizedBearings
    {n : Nat} (A : EuclideanLollipopArrangement n) : Prop :=
  ∀ i : Fin n, (A.lollipop i).HasNormalizedBearing

/-- Arrangement-level form of the close-direction-to-ray-dot bridge. -/
theorem dot2_rayDirection_nonneg_of_cyclicClose
    {n : Nat} {A : EuclideanLollipopArrangement n} {i j : Fin n}
    (hA : A.HasNormalizedBearings)
    (hclose :
      CloseDirection.cyclicClose
        (fun k => A.normalizedDirection k) i j) :
    0 ≤ dot2 (A.lollipop i).rayDirection (A.lollipop j).rayDirection := by
  exact
    EuclideanLollipop.dot2_rayDirection_nonneg_of_cyclicClosePair
      (hA i) (hA j)
      (by
        simpa [CloseDirection.cyclicClose,
          EuclideanLollipopArrangement.normalizedDirection] using hclose)

end EuclideanLollipopArrangement

end PrimitiveGeometry
end TheoremOneManuscript
end Lollipop
