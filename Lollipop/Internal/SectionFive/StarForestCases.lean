import Lollipop.Internal.Matrix.StarForest
import Mathlib.Tactic

/-!
Completion of the finite star-forest support cases for Section 5.

The earlier matrix files define the sixteen canonical star-forest masks in
`K_{3,4}` and prove the first five directly.  This file keeps the remaining
case split in a separate namespace/folder so the final theorem-one assembly can
import a single checked package of canonical star-forest minima.
-/

namespace Lollipop

/-- Canonical row-centered three-edge star case. -/
theorem canonical_shape3_row_minimum
    (U : NatMatrix) (hU : supportOfNat U = shape3_row) :
    matrixFNat U >= concreteM (matrixTotalNat U) := by
  have h03 : U 0 3 = 0 := entry_eq_zero_of_support_eq U hU (by simp [shape3_row])
  have h10 : U 1 0 = 0 := entry_eq_zero_of_support_eq U hU (by simp [shape3_row])
  have h11 : U 1 1 = 0 := entry_eq_zero_of_support_eq U hU (by simp [shape3_row])
  have h12 : U 1 2 = 0 := entry_eq_zero_of_support_eq U hU (by simp [shape3_row])
  have h13 : U 1 3 = 0 := entry_eq_zero_of_support_eq U hU (by simp [shape3_row])
  have h20 : U 2 0 = 0 := entry_eq_zero_of_support_eq U hU (by simp [shape3_row])
  have h21 : U 2 1 = 0 := entry_eq_zero_of_support_eq U hU (by simp [shape3_row])
  have h22 : U 2 2 = 0 := entry_eq_zero_of_support_eq U hU (by simp [shape3_row])
  have h23 : U 2 3 = 0 := entry_eq_zero_of_support_eq U hU (by simp [shape3_row])
  let a : Rat := (U 0 0 : Rat)
  let b : Rat := (U 0 1 : Rat)
  let c : Rat := (U 0 2 : Rat)
  have htotal : (matrixTotalNat U : Rat) = a + b + c := by
    simp [a, b, c, matrixTotalNat, Fin.sum_univ_three, Fin.sum_univ_four,
      h03, h10, h11, h12, h13, h20, h21, h22, h23]
  have hF : (a + b + c)^2 <= matrixFNat U := by
    simp [a, b, c, matrixFNat, matrixOfNat, matrixF, rowSum, colSum,
      Fin.sum_univ_three, Fin.sum_univ_four,
      h03, h10, h11, h12, h13, h20, h21, h22, h23]
    nlinarith [sq_nonneg a, sq_nonneg b, sq_nonneg c]
  exact matrix_theorem_of_one_component_star_bound U htotal le_rfl hF

/-- Canonical row-centered two-edge star plus one singleton case. -/
theorem canonical_shape3_row_plus_singleton_minimum
    (U : NatMatrix) (hU : supportOfNat U = shape3_row_plus_singleton) :
    matrixFNat U >= concreteM (matrixTotalNat U) := by
  have h02 : U 0 2 = 0 := entry_eq_zero_of_support_eq U hU
    (by simp [shape3_row_plus_singleton])
  have h03 : U 0 3 = 0 := entry_eq_zero_of_support_eq U hU
    (by simp [shape3_row_plus_singleton])
  have h10 : U 1 0 = 0 := entry_eq_zero_of_support_eq U hU
    (by simp [shape3_row_plus_singleton])
  have h11 : U 1 1 = 0 := entry_eq_zero_of_support_eq U hU
    (by simp [shape3_row_plus_singleton])
  have h13 : U 1 3 = 0 := entry_eq_zero_of_support_eq U hU
    (by simp [shape3_row_plus_singleton])
  have h20 : U 2 0 = 0 := entry_eq_zero_of_support_eq U hU
    (by simp [shape3_row_plus_singleton])
  have h21 : U 2 1 = 0 := entry_eq_zero_of_support_eq U hU
    (by simp [shape3_row_plus_singleton])
  have h22 : U 2 2 = 0 := entry_eq_zero_of_support_eq U hU
    (by simp [shape3_row_plus_singleton])
  have h23 : U 2 3 = 0 := entry_eq_zero_of_support_eq U hU
    (by simp [shape3_row_plus_singleton])
  let a : Rat := (U 0 0 : Rat)
  let b : Rat := (U 0 1 : Rat)
  let c : Rat := (U 1 2 : Rat)
  have htotal : (matrixTotalNat U : Rat) = (a + b) + c := by
    simp [a, b, c, matrixTotalNat, Fin.sum_univ_three, Fin.sum_univ_four,
      h02, h03, h10, h11, h13, h20, h21, h22, h23]
  have hF : (a + b)^2 + c^2 <= matrixFNat U := by
    simp [a, b, c, matrixFNat, matrixOfNat, matrixF, rowSum, colSum,
      Fin.sum_univ_three, Fin.sum_univ_four,
      h02, h03, h10, h11, h13, h20, h21, h22, h23]
    nlinarith [sq_nonneg a, sq_nonneg b, sq_nonneg c]
  exact matrix_theorem_of_two_component_star_bound U htotal le_rfl le_rfl hF

/-- Canonical column-centered three-edge star case. -/
theorem canonical_shape3_col_minimum
    (U : NatMatrix) (hU : supportOfNat U = shape3_col) :
    matrixFNat U >= concreteM (matrixTotalNat U) := by
  have h01 : U 0 1 = 0 := entry_eq_zero_of_support_eq U hU (by simp [shape3_col])
  have h02 : U 0 2 = 0 := entry_eq_zero_of_support_eq U hU (by simp [shape3_col])
  have h03 : U 0 3 = 0 := entry_eq_zero_of_support_eq U hU (by simp [shape3_col])
  have h11 : U 1 1 = 0 := entry_eq_zero_of_support_eq U hU (by simp [shape3_col])
  have h12 : U 1 2 = 0 := entry_eq_zero_of_support_eq U hU (by simp [shape3_col])
  have h13 : U 1 3 = 0 := entry_eq_zero_of_support_eq U hU (by simp [shape3_col])
  have h21 : U 2 1 = 0 := entry_eq_zero_of_support_eq U hU (by simp [shape3_col])
  have h22 : U 2 2 = 0 := entry_eq_zero_of_support_eq U hU (by simp [shape3_col])
  have h23 : U 2 3 = 0 := entry_eq_zero_of_support_eq U hU (by simp [shape3_col])
  let a : Rat := (U 0 0 : Rat)
  let b : Rat := (U 1 0 : Rat)
  let c : Rat := (U 2 0 : Rat)
  have htotal : (matrixTotalNat U : Rat) = a + b + c := by
    simp [a, b, c, matrixTotalNat, Fin.sum_univ_three, Fin.sum_univ_four,
      h01, h02, h03, h11, h12, h13, h21, h22, h23]
  have hF : (a + b + c)^2 <= matrixFNat U := by
    simp [a, b, c, matrixFNat, matrixOfNat, matrixF, rowSum, colSum,
      Fin.sum_univ_three, Fin.sum_univ_four,
      h01, h02, h03, h11, h12, h13, h21, h22, h23]
    nlinarith [sq_nonneg a, sq_nonneg b, sq_nonneg c]
  exact matrix_theorem_of_one_component_star_bound U htotal le_rfl hF

/-- Canonical column-centered two-edge star plus one singleton case. -/
theorem canonical_shape3_col_plus_singleton_minimum
    (U : NatMatrix) (hU : supportOfNat U = shape3_col_plus_singleton) :
    matrixFNat U >= concreteM (matrixTotalNat U) := by
  have h01 : U 0 1 = 0 := entry_eq_zero_of_support_eq U hU
    (by simp [shape3_col_plus_singleton])
  have h02 : U 0 2 = 0 := entry_eq_zero_of_support_eq U hU
    (by simp [shape3_col_plus_singleton])
  have h03 : U 0 3 = 0 := entry_eq_zero_of_support_eq U hU
    (by simp [shape3_col_plus_singleton])
  have h11 : U 1 1 = 0 := entry_eq_zero_of_support_eq U hU
    (by simp [shape3_col_plus_singleton])
  have h12 : U 1 2 = 0 := entry_eq_zero_of_support_eq U hU
    (by simp [shape3_col_plus_singleton])
  have h13 : U 1 3 = 0 := entry_eq_zero_of_support_eq U hU
    (by simp [shape3_col_plus_singleton])
  have h20 : U 2 0 = 0 := entry_eq_zero_of_support_eq U hU
    (by simp [shape3_col_plus_singleton])
  have h22 : U 2 2 = 0 := entry_eq_zero_of_support_eq U hU
    (by simp [shape3_col_plus_singleton])
  have h23 : U 2 3 = 0 := entry_eq_zero_of_support_eq U hU
    (by simp [shape3_col_plus_singleton])
  let a : Rat := (U 0 0 : Rat)
  let b : Rat := (U 1 0 : Rat)
  let c : Rat := (U 2 1 : Rat)
  have htotal : (matrixTotalNat U : Rat) = (a + b) + c := by
    simp [a, b, c, matrixTotalNat, Fin.sum_univ_three, Fin.sum_univ_four,
      h01, h02, h03, h11, h12, h13, h20, h22, h23]
  have hF : (a + b)^2 + c^2 <= matrixFNat U := by
    simp [a, b, c, matrixFNat, matrixOfNat, matrixF, rowSum, colSum,
      Fin.sum_univ_three, Fin.sum_univ_four,
      h01, h02, h03, h11, h12, h13, h20, h22, h23]
    nlinarith [sq_nonneg a, sq_nonneg b, sq_nonneg c]
  exact matrix_theorem_of_two_component_star_bound U htotal le_rfl le_rfl hF

/-- Canonical three singleton components case. -/
theorem canonical_shape3_singletons_minimum
    (U : NatMatrix) (hU : supportOfNat U = shape3_singletons) :
    matrixFNat U >= concreteM (matrixTotalNat U) := by
  have h01 : U 0 1 = 0 := entry_eq_zero_of_support_eq U hU (by simp [shape3_singletons])
  have h02 : U 0 2 = 0 := entry_eq_zero_of_support_eq U hU (by simp [shape3_singletons])
  have h03 : U 0 3 = 0 := entry_eq_zero_of_support_eq U hU (by simp [shape3_singletons])
  have h10 : U 1 0 = 0 := entry_eq_zero_of_support_eq U hU (by simp [shape3_singletons])
  have h12 : U 1 2 = 0 := entry_eq_zero_of_support_eq U hU (by simp [shape3_singletons])
  have h13 : U 1 3 = 0 := entry_eq_zero_of_support_eq U hU (by simp [shape3_singletons])
  have h20 : U 2 0 = 0 := entry_eq_zero_of_support_eq U hU (by simp [shape3_singletons])
  have h21 : U 2 1 = 0 := entry_eq_zero_of_support_eq U hU (by simp [shape3_singletons])
  have h23 : U 2 3 = 0 := entry_eq_zero_of_support_eq U hU (by simp [shape3_singletons])
  let a : Rat := (U 0 0 : Rat)
  let b : Rat := (U 1 1 : Rat)
  let c : Rat := (U 2 2 : Rat)
  have htotal : (matrixTotalNat U : Rat) = a + b + c := by
    simp [a, b, c, matrixTotalNat, Fin.sum_univ_three, Fin.sum_univ_four,
      h01, h02, h03, h10, h12, h13, h20, h21, h23]
  have hF :
      (3 / 2 : Rat) * a^2 +
        (3 / 2 : Rat) * b^2 +
          (3 / 2 : Rat) * c^2 <= matrixFNat U := by
    simp [a, b, c, matrixFNat, matrixOfNat, matrixF, rowSum, colSum,
      Fin.sum_univ_three, Fin.sum_univ_four,
      h01, h02, h03, h10, h12, h13, h20, h21, h23]
    nlinarith
  exact matrix_theorem_of_three_singleton_star_bound U htotal le_rfl le_rfl le_rfl hF

/-- Canonical row-centered four-edge star case. -/
theorem canonical_shape4_row_minimum
    (U : NatMatrix) (hU : supportOfNat U = shape4_row) :
    matrixFNat U >= concreteM (matrixTotalNat U) := by
  have h10 : U 1 0 = 0 := entry_eq_zero_of_support_eq U hU (by simp [shape4_row])
  have h11 : U 1 1 = 0 := entry_eq_zero_of_support_eq U hU (by simp [shape4_row])
  have h12 : U 1 2 = 0 := entry_eq_zero_of_support_eq U hU (by simp [shape4_row])
  have h13 : U 1 3 = 0 := entry_eq_zero_of_support_eq U hU (by simp [shape4_row])
  have h20 : U 2 0 = 0 := entry_eq_zero_of_support_eq U hU (by simp [shape4_row])
  have h21 : U 2 1 = 0 := entry_eq_zero_of_support_eq U hU (by simp [shape4_row])
  have h22 : U 2 2 = 0 := entry_eq_zero_of_support_eq U hU (by simp [shape4_row])
  have h23 : U 2 3 = 0 := entry_eq_zero_of_support_eq U hU (by simp [shape4_row])
  let a : Rat := (U 0 0 : Rat)
  let b : Rat := (U 0 1 : Rat)
  let c : Rat := (U 0 2 : Rat)
  let d : Rat := (U 0 3 : Rat)
  have htotal : (matrixTotalNat U : Rat) = a + b + c + d := by
    simp [a, b, c, d, matrixTotalNat, Fin.sum_univ_three, Fin.sum_univ_four,
      h10, h11, h12, h13, h20, h21, h22, h23]
  have hF : (a + b + c + d)^2 <= matrixFNat U := by
    simp [a, b, c, d, matrixFNat, matrixOfNat, matrixF, rowSum, colSum,
      Fin.sum_univ_three, Fin.sum_univ_four,
      h10, h11, h12, h13, h20, h21, h22, h23]
    nlinarith [sq_nonneg a, sq_nonneg b, sq_nonneg c, sq_nonneg d]
  exact matrix_theorem_of_one_component_star_bound U htotal le_rfl hF

/-- Canonical row-centered three-edge star plus one singleton case. -/
theorem canonical_shape4_row3_plus_singleton_minimum
    (U : NatMatrix) (hU : supportOfNat U = shape4_row3_plus_singleton) :
    matrixFNat U >= concreteM (matrixTotalNat U) := by
  have h03 : U 0 3 = 0 := entry_eq_zero_of_support_eq U hU
    (by simp [shape4_row3_plus_singleton])
  have h10 : U 1 0 = 0 := entry_eq_zero_of_support_eq U hU
    (by simp [shape4_row3_plus_singleton])
  have h11 : U 1 1 = 0 := entry_eq_zero_of_support_eq U hU
    (by simp [shape4_row3_plus_singleton])
  have h12 : U 1 2 = 0 := entry_eq_zero_of_support_eq U hU
    (by simp [shape4_row3_plus_singleton])
  have h20 : U 2 0 = 0 := entry_eq_zero_of_support_eq U hU
    (by simp [shape4_row3_plus_singleton])
  have h21 : U 2 1 = 0 := entry_eq_zero_of_support_eq U hU
    (by simp [shape4_row3_plus_singleton])
  have h22 : U 2 2 = 0 := entry_eq_zero_of_support_eq U hU
    (by simp [shape4_row3_plus_singleton])
  have h23 : U 2 3 = 0 := entry_eq_zero_of_support_eq U hU
    (by simp [shape4_row3_plus_singleton])
  let a : Rat := (U 0 0 : Rat)
  let b : Rat := (U 0 1 : Rat)
  let c : Rat := (U 0 2 : Rat)
  let d : Rat := (U 1 3 : Rat)
  have htotal : (matrixTotalNat U : Rat) = (a + b + c) + d := by
    simp [a, b, c, d, matrixTotalNat, Fin.sum_univ_three, Fin.sum_univ_four,
      h03, h10, h11, h12, h20, h21, h22, h23]
  have hF : (a + b + c)^2 + d^2 <= matrixFNat U := by
    simp [a, b, c, d, matrixFNat, matrixOfNat, matrixF, rowSum, colSum,
      Fin.sum_univ_three, Fin.sum_univ_four,
      h03, h10, h11, h12, h20, h21, h22, h23]
    nlinarith [sq_nonneg a, sq_nonneg b, sq_nonneg c, sq_nonneg d]
  exact matrix_theorem_of_two_component_star_bound U htotal le_rfl le_rfl hF

/-- Canonical two disjoint row-centered two-edge stars case. -/
theorem canonical_shape4_two_row2_minimum
    (U : NatMatrix) (hU : supportOfNat U = shape4_two_row2) :
    matrixFNat U >= concreteM (matrixTotalNat U) := by
  have h02 : U 0 2 = 0 := entry_eq_zero_of_support_eq U hU (by simp [shape4_two_row2])
  have h03 : U 0 3 = 0 := entry_eq_zero_of_support_eq U hU (by simp [shape4_two_row2])
  have h10 : U 1 0 = 0 := entry_eq_zero_of_support_eq U hU (by simp [shape4_two_row2])
  have h11 : U 1 1 = 0 := entry_eq_zero_of_support_eq U hU (by simp [shape4_two_row2])
  have h20 : U 2 0 = 0 := entry_eq_zero_of_support_eq U hU (by simp [shape4_two_row2])
  have h21 : U 2 1 = 0 := entry_eq_zero_of_support_eq U hU (by simp [shape4_two_row2])
  have h22 : U 2 2 = 0 := entry_eq_zero_of_support_eq U hU (by simp [shape4_two_row2])
  have h23 : U 2 3 = 0 := entry_eq_zero_of_support_eq U hU (by simp [shape4_two_row2])
  let a : Rat := (U 0 0 : Rat)
  let b : Rat := (U 0 1 : Rat)
  let c : Rat := (U 1 2 : Rat)
  let d : Rat := (U 1 3 : Rat)
  have htotal : (matrixTotalNat U : Rat) = (a + b) + (c + d) := by
    simp [a, b, c, d, matrixTotalNat, Fin.sum_univ_three, Fin.sum_univ_four,
      h02, h03, h10, h11, h20, h21, h22, h23]
  have hF : (a + b)^2 + (c + d)^2 <= matrixFNat U := by
    simp [a, b, c, d, matrixFNat, matrixOfNat, matrixF, rowSum, colSum,
      Fin.sum_univ_three, Fin.sum_univ_four,
      h02, h03, h10, h11, h20, h21, h22, h23]
    nlinarith [sq_nonneg a, sq_nonneg b, sq_nonneg c, sq_nonneg d]
  exact matrix_theorem_of_two_component_star_bound U htotal le_rfl le_rfl hF

/-- Canonical row-centered two-edge star and column-centered two-edge star case. -/
theorem canonical_shape4_row2_col2_minimum
    (U : NatMatrix) (hU : supportOfNat U = shape4_row2_col2) :
    matrixFNat U >= concreteM (matrixTotalNat U) := by
  have h02 : U 0 2 = 0 := entry_eq_zero_of_support_eq U hU (by simp [shape4_row2_col2])
  have h03 : U 0 3 = 0 := entry_eq_zero_of_support_eq U hU (by simp [shape4_row2_col2])
  have h10 : U 1 0 = 0 := entry_eq_zero_of_support_eq U hU (by simp [shape4_row2_col2])
  have h11 : U 1 1 = 0 := entry_eq_zero_of_support_eq U hU (by simp [shape4_row2_col2])
  have h13 : U 1 3 = 0 := entry_eq_zero_of_support_eq U hU (by simp [shape4_row2_col2])
  have h20 : U 2 0 = 0 := entry_eq_zero_of_support_eq U hU (by simp [shape4_row2_col2])
  have h21 : U 2 1 = 0 := entry_eq_zero_of_support_eq U hU (by simp [shape4_row2_col2])
  have h23 : U 2 3 = 0 := entry_eq_zero_of_support_eq U hU (by simp [shape4_row2_col2])
  let a : Rat := (U 0 0 : Rat)
  let b : Rat := (U 0 1 : Rat)
  let c : Rat := (U 1 2 : Rat)
  let d : Rat := (U 2 2 : Rat)
  have htotal : (matrixTotalNat U : Rat) = (a + b) + (c + d) := by
    simp [a, b, c, d, matrixTotalNat, Fin.sum_univ_three, Fin.sum_univ_four,
      h02, h03, h10, h11, h13, h20, h21, h23]
    ring
  have hF : (a + b)^2 + (c + d)^2 <= matrixFNat U := by
    simp [a, b, c, d, matrixFNat, matrixOfNat, matrixF, rowSum, colSum,
      Fin.sum_univ_three, Fin.sum_univ_four,
      h02, h03, h10, h11, h13, h20, h21, h23]
    nlinarith [sq_nonneg a, sq_nonneg b, sq_nonneg c, sq_nonneg d]
  exact matrix_theorem_of_two_component_star_bound U htotal le_rfl le_rfl hF

/-- Canonical exceptional `(2,1,1)` star-forest case. -/
theorem canonical_shape4_exceptional_minimum
    (U : NatMatrix) (hU : supportOfNat U = shape4_exceptional) :
    matrixFNat U >= concreteM (matrixTotalNat U) := by
  have h02 : U 0 2 = 0 := entry_eq_zero_of_support_eq U hU (by simp [shape4_exceptional])
  have h03 : U 0 3 = 0 := entry_eq_zero_of_support_eq U hU (by simp [shape4_exceptional])
  have h10 : U 1 0 = 0 := entry_eq_zero_of_support_eq U hU (by simp [shape4_exceptional])
  have h11 : U 1 1 = 0 := entry_eq_zero_of_support_eq U hU (by simp [shape4_exceptional])
  have h13 : U 1 3 = 0 := entry_eq_zero_of_support_eq U hU (by simp [shape4_exceptional])
  have h20 : U 2 0 = 0 := entry_eq_zero_of_support_eq U hU (by simp [shape4_exceptional])
  have h21 : U 2 1 = 0 := entry_eq_zero_of_support_eq U hU (by simp [shape4_exceptional])
  have h22 : U 2 2 = 0 := entry_eq_zero_of_support_eq U hU (by simp [shape4_exceptional])
  have htotal :
      matrixTotalNat U = U 0 0 + U 0 1 + U 1 2 + U 2 3 := by
    simp [matrixTotalNat, Fin.sum_univ_three, Fin.sum_univ_four,
      h02, h03, h10, h11, h13, h20, h21, h22]
  have hF :
      quadCost (U 0 0 : Rat) (U 0 1 : Rat) (U 1 2 : Rat) (U 2 3 : Rat) <=
        matrixFNat U := by
    simp [quadCost, matrixFNat, matrixOfNat, matrixF, rowSum, colSum,
      Fin.sum_univ_three, Fin.sum_univ_four,
      h02, h03, h10, h11, h13, h20, h21, h22]
    nlinarith
  exact matrix_theorem_of_exceptional_star_quad_bound U htotal hF

/-- Canonical five-edge `(3,2)` star-forest case. -/
theorem canonical_shape5_row3_col2_minimum
    (U : NatMatrix) (hU : supportOfNat U = shape5_row3_col2) :
    matrixFNat U >= concreteM (matrixTotalNat U) := by
  have h03 : U 0 3 = 0 := entry_eq_zero_of_support_eq U hU (by simp [shape5_row3_col2])
  have h10 : U 1 0 = 0 := entry_eq_zero_of_support_eq U hU (by simp [shape5_row3_col2])
  have h11 : U 1 1 = 0 := entry_eq_zero_of_support_eq U hU (by simp [shape5_row3_col2])
  have h12 : U 1 2 = 0 := entry_eq_zero_of_support_eq U hU (by simp [shape5_row3_col2])
  have h20 : U 2 0 = 0 := entry_eq_zero_of_support_eq U hU (by simp [shape5_row3_col2])
  have h21 : U 2 1 = 0 := entry_eq_zero_of_support_eq U hU (by simp [shape5_row3_col2])
  have h22 : U 2 2 = 0 := entry_eq_zero_of_support_eq U hU (by simp [shape5_row3_col2])
  let a : Rat := (U 0 0 : Rat)
  let b : Rat := (U 0 1 : Rat)
  let c : Rat := (U 0 2 : Rat)
  let d : Rat := (U 1 3 : Rat)
  let e : Rat := (U 2 3 : Rat)
  have htotal : (matrixTotalNat U : Rat) = (a + b + c) + (d + e) := by
    simp [a, b, c, d, e, matrixTotalNat, Fin.sum_univ_three, Fin.sum_univ_four,
      h03, h10, h11, h12, h20, h21, h22]
    ring
  have hF : (a + b + c)^2 + (d + e)^2 <= matrixFNat U := by
    simp [a, b, c, d, e, matrixFNat, matrixOfNat, matrixF, rowSum, colSum,
      Fin.sum_univ_three, Fin.sum_univ_four,
      h03, h10, h11, h12, h20, h21, h22]
    nlinarith [sq_nonneg a, sq_nonneg b, sq_nonneg c, sq_nonneg d, sq_nonneg e]
  exact matrix_theorem_of_two_component_star_bound U htotal le_rfl le_rfl hF

/-- All sixteen canonical star-forest support cases satisfy the matrix
minimum. -/
theorem canonicalStarForestMinimumCases_proven :
    CanonicalStarForestMinimumCases := by
  intro U T hT hU
  simp [canonicalStarForestSupports] at hT
  rcases hT with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact canonical_shape0_minimum U hU
  · exact canonical_shape1_minimum U hU
  · exact canonical_shape2_row_minimum U hU
  · exact canonical_shape2_col_minimum U hU
  · exact canonical_shape2_singletons_minimum U hU
  · exact canonical_shape3_row_minimum U hU
  · exact canonical_shape3_row_plus_singleton_minimum U hU
  · exact canonical_shape3_col_minimum U hU
  · exact canonical_shape3_col_plus_singleton_minimum U hU
  · exact canonical_shape3_singletons_minimum U hU
  · exact canonical_shape4_row_minimum U hU
  · exact canonical_shape4_row3_plus_singleton_minimum U hU
  · exact canonical_shape4_two_row2_minimum U hU
  · exact canonical_shape4_row2_col2_minimum U hU
  · exact canonical_shape4_exceptional_minimum U hU
  · exact canonical_shape5_row3_col2_minimum U hU

/-- The star-forest minimum, with all finite canonical cases discharged. -/
theorem starForestMinimum_proven : StarForestMinimumStatement :=
  starForestMinimum_of_canonical_cases canonicalStarForestMinimumCases_proven

end Lollipop
