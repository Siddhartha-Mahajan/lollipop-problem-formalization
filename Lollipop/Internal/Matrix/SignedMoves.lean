import Lollipop.Internal.Matrix.Basic
import Mathlib.Tactic

/-!
Generic signed-move algebra for Section 5 compression.

The cycle and four-edge path compressions both move along an integer direction
`D` whose total mass is zero and whose quadratic coefficient for `matrixF` is
nonpositive.  The core analytic fact is independent of the graph bookkeeping:
for a quadratic `q(t) = b t + a t^2` with `a <= 0` and `q(0)=0`, one of the
two endpoints of any interval around zero has `q <= 0`.
-/

namespace Lollipop

open BigOperators

/-- Add a rational direction to a rational matrix. -/
def addDir (U D : Fin 3 → Fin 4 → ℚ) (t : ℚ) : Fin 3 → Fin 4 → ℚ :=
  fun i j => U i j + t * D i j

/-- The quadratic expansion of `matrixF` along an arbitrary direction. -/
theorem matrixF_addDir_sub
    (U D : Fin 3 → Fin 4 → ℚ) (t : ℚ) :
    matrixF (addDir U D t) - matrixF U =
      t * (matrixF (addDir U D 1) - matrixF U - matrixF D) +
        t^2 * matrixF D := by
  simp [matrixF, rowSum, colSum, addDir, Fin.sum_univ_three, Fin.sum_univ_four]
  ring

/-- A concave or linear quadratic vanishing at `0` is nonpositive at one of
two opposite endpoints. -/
theorem endpoint_quadratic_nonpos
    {a b P N : ℚ} (ha : a ≤ 0) (hP : 0 ≤ P) (hN : 0 ≤ N) :
    N * b + N^2 * a ≤ 0 ∨ (-P) * b + (-P)^2 * a ≤ 0 := by
  by_contra h
  push Not at h
  have hNpos : 0 < N := by
    by_contra hNnot
    have hNz : N = 0 := le_antisymm (le_of_not_gt hNnot) hN
    subst N
    norm_num at h
  have hPpos : 0 < P := by
    by_contra hPnot
    have hPz : P = 0 := le_antisymm (le_of_not_gt hPnot) hP
    subst P
    norm_num at h
  have hb_low : -N * a < b := by
    nlinarith [div_pos h.1 hNpos]
  have hb_high : b < P * a := by
    nlinarith [div_pos h.2 hPpos]
  have hpa_nonpos : P * a ≤ 0 := mul_nonpos_of_nonneg_of_nonpos hP ha
  have hnona : 0 ≤ -N * a := by
    nlinarith [mul_nonpos_of_nonneg_of_nonpos hN ha]
  nlinarith

/-- If the quadratic coefficient of `matrixF` along `D` is nonpositive, then
one of the two endpoint moves has non-increasing `matrixF`. -/
theorem matrixF_addDir_endpoint_nonincreasing
    (U D : Fin 3 → Fin 4 → ℚ) {P N : ℚ}
    (hquad : matrixF D ≤ 0) (hP : 0 ≤ P) (hN : 0 ≤ N) :
    matrixF (addDir U D N) ≤ matrixF U ∨
      matrixF (addDir U D (-P)) ≤ matrixF U := by
  let b := matrixF (addDir U D 1) - matrixF U - matrixF D
  have hend := endpoint_quadratic_nonpos
    (a := matrixF D) (b := b) hquad hP hN
  rcases hend with hend | hend
  · left
    rw [← sub_nonpos, matrixF_addDir_sub]
    exact hend
  · right
    rw [← sub_nonpos, matrixF_addDir_sub]
    exact hend

end Lollipop
