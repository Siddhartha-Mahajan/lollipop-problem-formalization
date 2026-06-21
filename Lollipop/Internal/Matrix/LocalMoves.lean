import Lollipop.Internal.Matrix.SignedMoves
import Mathlib.Tactic

/-!
Actual `matrixF` identities for the local compression moves in Section 5.

`CompressionAlgebra.lean` proves abstract polynomial fragments.  This module
ties representative moves directly to the `3 x 4` matrix quadratic form.
Permuted versions follow by relabelling rows and columns; the global
bookkeeping still remains to be formalized.
-/

namespace Lollipop

open BigOperators

/-- Canonical four-cycle alternating move on rows `0,1` and columns `0,1`. -/
def cycleMove (U : Fin 3 → Fin 4 → ℚ) (eps : ℚ) : Fin 3 → Fin 4 → ℚ :=
  fun i j =>
    if i = 0 ∧ j = 0 then U i j + eps else
    if i = 0 ∧ j = 1 then U i j - eps else
    if i = 1 ∧ j = 1 then U i j + eps else
    if i = 1 ∧ j = 0 then U i j - eps else
    U i j

/-- The canonical four-cycle move has the concave quadratic change asserted
in Section 5. -/
theorem matrixF_cycleMove_sub
    (U : Fin 3 → Fin 4 → ℚ) (eps : ℚ) :
    matrixF (cycleMove U eps) - matrixF U =
      eps * (-(U 0 0) + U 0 1 - U 1 1 + U 1 0) - 2 * eps^2 := by
  simp [matrixF, rowSum, colSum, cycleMove, Fin.sum_univ_three, Fin.sum_univ_four]
  ring

/-- For the canonical four-cycle move, one endpoint of any interval around
zero is non-increasing for `matrixF`. -/
theorem matrixF_cycleMove_endpoint_nonincreasing
    (U : Fin 3 → Fin 4 → ℚ) {P N : ℚ}
    (hP : 0 ≤ P) (hN : 0 ≤ N) :
    matrixF (cycleMove U N) ≤ matrixF U ∨
      matrixF (cycleMove U (-P)) ≤ matrixF U := by
  let b := -(U 0 0) + U 0 1 - U 1 1 + U 1 0
  have hend := endpoint_quadratic_nonpos
    (a := (-2 : ℚ)) (b := b) (by norm_num) hP hN
  rcases hend with hend | hend
  · left
    rw [← sub_nonpos, matrixF_cycleMove_sub]
    nlinarith
  · right
    rw [← sub_nonpos, matrixF_cycleMove_sub]
    nlinarith

/-- Canonical four-edge path move on the path
`row 0 - col 0 - row 1 - col 1 - row 2`. -/
def pathMove (U : Fin 3 → Fin 4 → ℚ) (eps : ℚ) : Fin 3 → Fin 4 → ℚ :=
  fun i j =>
    if i = 0 ∧ j = 0 then U i j + eps else
    if i = 1 ∧ j = 0 then U i j - eps else
    if i = 1 ∧ j = 1 then U i j + eps else
    if i = 2 ∧ j = 1 then U i j - eps else
    U i j

/-- The canonical four-edge path move has zero quadratic coefficient, hence
the change in `F` is linear in the compression parameter. -/
theorem matrixF_pathMove_sub
    (U : Fin 3 → Fin 4 → ℚ) (eps : ℚ) :
    matrixF (pathMove U eps) - matrixF U =
      eps *
        (2 * rowSum U 0 - 2 * rowSum U 2 -
          U 0 0 + U 1 0 - U 1 1 + U 2 1) := by
  simp [matrixF, rowSum, colSum, pathMove, Fin.sum_univ_three, Fin.sum_univ_four]
  ring

/-- For the canonical four-edge path move, one endpoint of any interval around
zero is non-increasing for `matrixF`. -/
theorem matrixF_pathMove_endpoint_nonincreasing
    (U : Fin 3 → Fin 4 → ℚ) {P N : ℚ}
    (hP : 0 ≤ P) (hN : 0 ≤ N) :
    matrixF (pathMove U N) ≤ matrixF U ∨
      matrixF (pathMove U (-P)) ≤ matrixF U := by
  let b :=
    2 * rowSum U 0 - 2 * rowSum U 2 -
      U 0 0 + U 1 0 - U 1 1 + U 2 1
  have hend := endpoint_quadratic_nonpos
    (a := (0 : ℚ)) (b := b) (by norm_num) hP hN
  rcases hend with hend | hend
  · left
    rw [← sub_nonpos, matrixF_pathMove_sub]
    nlinarith
  · right
    rw [← sub_nonpos, matrixF_pathMove_sub]
    nlinarith

/-- Canonical double-star component with central edge `(0,0)`, selected
row-side leaf `(0,1)`, selected column-side leaf `(1,0)`, two other row-side
leaf masses, and one other column-side leaf mass. -/
def canonicalDoubleStar (x y z A1 A2 B : ℚ) : Fin 3 → Fin 4 → ℚ :=
  fun i j =>
    if i = 0 ∧ j = 1 then x else
    if i = 0 ∧ j = 0 then y else
    if i = 1 ∧ j = 0 then z else
    if i = 0 ∧ j = 2 then A1 else
    if i = 0 ∧ j = 3 then A2 else
    if i = 2 ∧ j = 0 then B else 0

/-- Delete the central edge and move its mass to the selected row-side leaf. -/
def canonicalDoubleStarMoveX (x y z A1 A2 B : ℚ) : Fin 3 → Fin 4 → ℚ :=
  fun i j =>
    if i = 0 ∧ j = 1 then x + y else
    if i = 0 ∧ j = 0 then 0 else
    if i = 1 ∧ j = 0 then z else
    if i = 0 ∧ j = 2 then A1 else
    if i = 0 ∧ j = 3 then A2 else
    if i = 2 ∧ j = 0 then B else 0

/-- Delete the central edge and move its mass to the selected column-side
leaf. -/
def canonicalDoubleStarMoveZ (x y z A1 A2 B : ℚ) : Fin 3 → Fin 4 → ℚ :=
  fun i j =>
    if i = 0 ∧ j = 1 then x else
    if i = 0 ∧ j = 0 then 0 else
    if i = 1 ∧ j = 0 then z + y else
    if i = 0 ∧ j = 2 then A1 else
    if i = 0 ∧ j = 3 then A2 else
    if i = 2 ∧ j = 0 then B else 0

/-- Actual `matrixF` identity for the first canonical double-star deletion. -/
theorem matrixF_canonicalDoubleStar_sub_moveX
    (x y z A1 A2 B : ℚ) :
    matrixF (canonicalDoubleStar x y z A1 A2 B) -
      matrixF (canonicalDoubleStarMoveX x y z A1 A2 B) =
      y * (2 * B + 2 * z - x) := by
  simp [matrixF, rowSum, colSum, canonicalDoubleStar, canonicalDoubleStarMoveX,
    Fin.sum_univ_three, Fin.sum_univ_four]
  ring

/-- Actual `matrixF` identity for the second canonical double-star deletion. -/
theorem matrixF_canonicalDoubleStar_sub_moveZ
    (x y z A1 A2 B : ℚ) :
    matrixF (canonicalDoubleStar x y z A1 A2 B) -
      matrixF (canonicalDoubleStarMoveZ x y z A1 A2 B) =
      y * (2 * (A1 + A2) + 2 * x - z) := by
  simp [matrixF, rowSum, colSum, canonicalDoubleStar, canonicalDoubleStarMoveZ,
    Fin.sum_univ_three, Fin.sum_univ_four]
  ring

end Lollipop
