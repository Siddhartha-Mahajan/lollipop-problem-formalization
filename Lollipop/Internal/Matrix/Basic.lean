import Lollipop.Internal.Formula
import Mathlib.Tactic

/-!
Basic natural-matrix form of the `3 x 4` matrix theorem.

The manuscript's matrix theorem is about nonnegative integer matrices.  This
module fixes that exact type and proves the unconditional small-total and
exceptional-star branches used in Section 5.
-/

namespace Lollipop

open BigOperators

/-- A `3 x 4` matrix with nonnegative integer entries. -/
abbrev NatMatrix := Fin 3 → Fin 4 → ℕ

/-- Coerce a natural matrix to the rational matrix used by `matrixF`. -/
def matrixOfNat (U : NatMatrix) : Fin 3 → Fin 4 → ℚ :=
  fun i j => (U i j : ℚ)

/-- Rational value of the matrix quadratic form on a natural matrix. -/
def matrixFNat (U : NatMatrix) : ℚ :=
  matrixF (matrixOfNat U)

/-- Sum of squares of all entries of a natural matrix, as a rational. -/
def entrySqNat (U : NatMatrix) : ℚ :=
  ∑ i : Fin 3, ∑ j : Fin 4, (U i j : ℚ)^2

/-- Total mass of a natural matrix. -/
def matrixTotalNat (U : NatMatrix) : ℕ :=
  ∑ i : Fin 3, ∑ j : Fin 4, U i j

/-- Section 5's matrix theorem, stated for the exact integer matrix type. -/
def MatrixTheoremStatement : Prop :=
  ∀ U : NatMatrix, matrixFNat U ≥ concreteM (matrixTotalNat U)

/-- Natural numbers satisfy `m <= m^2` after coercion to `ℚ`. -/
theorem nat_cast_le_sq (m : ℕ) : (m : ℚ) ≤ (m : ℚ)^2 := by
  cases m with
  | zero => norm_num
  | succ k =>
      have h : (1 : ℚ) ≤ (Nat.succ k : ℚ) := by
        exact_mod_cast Nat.succ_le_succ (Nat.zero_le k)
      nlinarith

/-- Every natural `3 x 4` matrix has `F(U) >= 3 * total(U) / 2`.
This is the nonnegativity expansion used for the small-`n` branch of
Section 5. -/
theorem three_halves_total_le_matrixFNat (U : NatMatrix) :
    (3 / 2 : ℚ) * (matrixTotalNat U : ℚ) ≤ matrixFNat U := by
  have h00 := nat_cast_le_sq (U 0 0)
  have h01 := nat_cast_le_sq (U 0 1)
  have h02 := nat_cast_le_sq (U 0 2)
  have h03 := nat_cast_le_sq (U 0 3)
  have h10 := nat_cast_le_sq (U 1 0)
  have h11 := nat_cast_le_sq (U 1 1)
  have h12 := nat_cast_le_sq (U 1 2)
  have h13 := nat_cast_le_sq (U 1 3)
  have h20 := nat_cast_le_sq (U 2 0)
  have h21 := nat_cast_le_sq (U 2 1)
  have h22 := nat_cast_le_sq (U 2 2)
  have h23 := nat_cast_le_sq (U 2 3)
  simp [matrixFNat, matrixOfNat, matrixF, rowSum, colSum, matrixTotalNat,
    Fin.sum_univ_three, Fin.sum_univ_four]
  nlinarith

set_option maxHeartbeats 800000 in
/-- The entry-square part alone contributes at least `3/2 * sum u_ij^2` to
`F`; all row/column cross terms are nonnegative for natural matrices. -/
theorem three_halves_entrySqNat_le_matrixFNat (U : NatMatrix) :
    (3 / 2 : ℚ) * entrySqNat U ≤ matrixFNat U := by
  have h00 : 0 ≤ (U 0 0 : ℚ) := by positivity
  have h01 : 0 ≤ (U 0 1 : ℚ) := by positivity
  have h02 : 0 ≤ (U 0 2 : ℚ) := by positivity
  have h03 : 0 ≤ (U 0 3 : ℚ) := by positivity
  have h10 : 0 ≤ (U 1 0 : ℚ) := by positivity
  have h11 : 0 ≤ (U 1 1 : ℚ) := by positivity
  have h12 : 0 ≤ (U 1 2 : ℚ) := by positivity
  have h13 : 0 ≤ (U 1 3 : ℚ) := by positivity
  have h20 : 0 ≤ (U 2 0 : ℚ) := by positivity
  have h21 : 0 ≤ (U 2 1 : ℚ) := by positivity
  have h22 : 0 ≤ (U 2 2 : ℚ) := by positivity
  have h23 : 0 ≤ (U 2 3 : ℚ) := by positivity
  simp [matrixFNat, matrixOfNat, matrixF, rowSum, colSum, entrySqNat,
    Fin.sum_univ_three, Fin.sum_univ_four]
  nlinarith [mul_nonneg h00 h01, mul_nonneg h00 h02, mul_nonneg h00 h03,
    mul_nonneg h01 h02, mul_nonneg h01 h03, mul_nonneg h02 h03,
    mul_nonneg h10 h11, mul_nonneg h10 h12, mul_nonneg h10 h13,
    mul_nonneg h11 h12, mul_nonneg h11 h13, mul_nonneg h12 h13,
    mul_nonneg h20 h21, mul_nonneg h20 h22, mul_nonneg h20 h23,
    mul_nonneg h21 h22, mul_nonneg h21 h23, mul_nonneg h22 h23,
    mul_nonneg h00 h10, mul_nonneg h00 h20, mul_nonneg h10 h20,
    mul_nonneg h01 h11, mul_nonneg h01 h21, mul_nonneg h11 h21,
    mul_nonneg h02 h12, mul_nonneg h02 h22, mul_nonneg h12 h22,
    mul_nonneg h03 h13, mul_nonneg h03 h23, mul_nonneg h13 h23]

/-- The matrix theorem for total mass at most three. -/
theorem matrix_theorem_of_total_le_three
    (U : NatMatrix) (hsmall : matrixTotalNat U ≤ 3) :
    matrixFNat U ≥ concreteM (matrixTotalNat U) := by
  have hF := three_halves_total_le_matrixFNat U
  have hM :=
    concreteM_eq_three_halves_mul_of_le_three
      (n := matrixTotalNat U) hsmall
  rw [hM]
  exact hF

/-- The exceptional `(2,1,1)` star normal form. -/
def exceptionalStarNat (a b c d : ℕ) : NatMatrix :=
  fun i : Fin 3 => fun j : Fin 4 =>
    if i = 0 ∧ j = 0 then a else
    if i = 0 ∧ j = 1 then b else
    if i = 1 ∧ j = 2 then c else
    if i = 2 ∧ j = 3 then d else 0

/-- The exceptional star normal form has total mass `a+b+c+d`. -/
theorem matrixTotalNat_exceptionalStarNat (a b c d : ℕ) :
    matrixTotalNat (exceptionalStarNat a b c d) = a + b + c + d := by
  simp [matrixTotalNat, exceptionalStarNat, Fin.sum_univ_three, Fin.sum_univ_four]

/-- Value of `F` on the exceptional star normal form. -/
theorem matrixFNat_exceptionalStarNat (a b c d : ℕ) :
    matrixFNat (exceptionalStarNat a b c d) =
      quadCost (a : ℚ) (b : ℚ) (c : ℚ) (d : ℚ) := by
  unfold matrixFNat matrixOfNat exceptionalStarNat
  simpa using matrixF_star (a : ℚ) (b : ℚ) (c : ℚ) (d : ℚ)

/-- The matrix theorem on the exceptional star normal form. -/
theorem matrix_theorem_exceptionalStarNat (a b c d : ℕ) :
    matrixFNat (exceptionalStarNat a b c d) ≥
      concreteM (matrixTotalNat (exceptionalStarNat a b c d)) := by
  rw [matrixTotalNat_exceptionalStarNat, matrixFNat_exceptionalStarNat]
  exact concreteM_le_quadCost_of_sum (a := a) (b := b) (c := c) (d := d) rfl

end Lollipop
