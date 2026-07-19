import Lollipop.Lemma_7_2.Proof
import Mathlib.Algebra.Order.Chebyshev
import Mathlib.Tactic

/-!
This is the substantive proof compilation unit for `Lemma_7_3`.
All project proof components used below are integrated here or imported
directly from another manuscript-numbered `Proof.lean` file.
-/

/-!
Proof component 2: `Matrix.StarForest`.
The complete checked source follows; it is part of this numbered proof
module rather than an import from a generic project support directory.
-/

/-!
Star-forest branch helpers for Section 5.

These lemmas bridge the abstract star-component inequalities to the concrete
finite minimum `M(n)`.  They do not yet extract the component summaries from
`IsSupportStarForest`; that graph bookkeeping is separate.  Once such summaries
are available, these lemmas discharge the non-exceptional star-forest cases.
-/

namespace Lollipop

/-- The finite set of canonical star-forest cases needed after support-shape
classification. -/
def CanonicalStarForestMinimumCases : Prop :=
  ∀ U : NatMatrix, ∀ T : Finset MatrixEdge,
    T ∈ canonicalStarForestSupports →
      supportOfNat U = T →
        matrixFNat U ≥ concreteM (matrixTotalNat U)

/-- The star-forest minimum follows from the finitely many canonical support
cases. -/
theorem starForestMinimum_of_canonical_cases
    (hcases : CanonicalStarForestMinimumCases) :
    StarForestMinimumStatement := by
  intro U hstar
  have hshape := canonicalShape_of_isSupportStarForest (S := supportOfNat U) hstar
  unfold IsCanonicalStarForestShape allCanonicalStarForestShapes at hshape
  rcases Finset.mem_biUnion.mp hshape with ⟨T, hT, hrelT⟩
  unfold relabeledStarForestSupportsOf at hrelT
  rcases Finset.mem_biUnion.mp hrelT with ⟨er, _her, hrelEr⟩
  rcases Finset.mem_image.mp hrelEr with ⟨ec, _hec, hsupport⟩
  let V := relabelNatMatrix er ec U
  have hVsupport : supportOfNat V = T := by
    exact supportOfNat_relabelNatMatrix_eq_of_supportRelabel
      er ec U T hsupport.symm
  have hV := hcases V T hT hVsupport
  unfold V at hV
  rw [matrixFNat_relabelNatMatrix, matrixTotalNat_relabelNatMatrix] at hV
  exact hV

/-- The matrix theorem follows from one-step support descent and the finitely
many canonical star-forest support cases. -/
theorem matrix_theorem_of_descent_step_and_canonical_cases
    (hstep : SupportDescentStepStatement)
    (hcases : CanonicalStarForestMinimumCases) :
    MatrixTheoremStatement := by
  exact matrix_theorem_of_descent_step_and_star_forest hstep
    (starForestMinimum_of_canonical_cases hcases)

/-- One star component with cost at least the square of its total mass gives
the matrix theorem. -/
theorem matrix_theorem_of_one_component_star_bound
    (U : NatMatrix)
    {s c : ℚ}
    (htotal : (matrixTotalNat U : ℚ) = s)
    (hc : s^2 ≤ c)
    (hF : c ≤ matrixFNat U) :
    matrixFNat U ≥ concreteM (matrixTotalNat U) := by
  by_cases hsmall : matrixTotalNat U ≤ 3
  · exact matrix_theorem_of_total_le_three U hsmall
  · have hlarge : 4 ≤ matrixTotalNat U := by omega
    apply matrix_theorem_of_half_sq_bound_of_total_ge_four U hlarge
    rw [htotal]
    nlinarith [hc, hF, sq_nonneg s]

/-- At most two star components give the manuscript's `n^2 / 2` lower bound,
hence the matrix theorem. -/
theorem matrix_theorem_of_two_component_star_bound
    (U : NatMatrix)
    {s₀ s₁ c₀ c₁ : ℚ}
    (htotal : (matrixTotalNat U : ℚ) = s₀ + s₁)
    (hc₀ : s₀^2 ≤ c₀)
    (hc₁ : s₁^2 ≤ c₁)
    (hF : c₀ + c₁ ≤ matrixFNat U) :
    matrixFNat U ≥ concreteM (matrixTotalNat U) := by
  by_cases hsmall : matrixTotalNat U ≤ 3
  · exact matrix_theorem_of_total_le_three U hsmall
  · have hlarge : 4 ≤ matrixTotalNat U := by omega
    apply matrix_theorem_of_half_sq_bound_of_total_ge_four U hlarge
    rw [htotal]
    exact (two_component_half_bound hc₀ hc₁).trans hF

/-- Canonical empty support case of the star-forest minimum. -/
theorem canonical_shape0_minimum
    (U : NatMatrix) (hU : supportOfNat U = shape0) :
    matrixFNat U ≥ concreteM (matrixTotalNat U) := by
  have h00 : U 0 0 = 0 := entry_eq_zero_of_not_mem_support U (by rw [hU]; simp [shape0])
  have h01 : U 0 1 = 0 := entry_eq_zero_of_not_mem_support U (by rw [hU]; simp [shape0])
  have h02 : U 0 2 = 0 := entry_eq_zero_of_not_mem_support U (by rw [hU]; simp [shape0])
  have h03 : U 0 3 = 0 := entry_eq_zero_of_not_mem_support U (by rw [hU]; simp [shape0])
  have h10 : U 1 0 = 0 := entry_eq_zero_of_not_mem_support U (by rw [hU]; simp [shape0])
  have h11 : U 1 1 = 0 := entry_eq_zero_of_not_mem_support U (by rw [hU]; simp [shape0])
  have h12 : U 1 2 = 0 := entry_eq_zero_of_not_mem_support U (by rw [hU]; simp [shape0])
  have h13 : U 1 3 = 0 := entry_eq_zero_of_not_mem_support U (by rw [hU]; simp [shape0])
  have h20 : U 2 0 = 0 := entry_eq_zero_of_not_mem_support U (by rw [hU]; simp [shape0])
  have h21 : U 2 1 = 0 := entry_eq_zero_of_not_mem_support U (by rw [hU]; simp [shape0])
  have h22 : U 2 2 = 0 := entry_eq_zero_of_not_mem_support U (by rw [hU]; simp [shape0])
  have h23 : U 2 3 = 0 := entry_eq_zero_of_not_mem_support U (by rw [hU]; simp [shape0])
  exact matrix_theorem_of_total_le_three U (by
    simp [matrixTotalNat, Fin.sum_univ_three, Fin.sum_univ_four,
      h00, h01, h02, h03, h10, h11, h12, h13, h20, h21, h22, h23])

/-- Canonical one-edge support case of the star-forest minimum. -/
theorem canonical_shape1_minimum
    (U : NatMatrix) (hU : supportOfNat U = shape1) :
    matrixFNat U ≥ concreteM (matrixTotalNat U) := by
  have h01 : U 0 1 = 0 := entry_eq_zero_of_not_mem_support U (by rw [hU]; simp [shape1])
  have h02 : U 0 2 = 0 := entry_eq_zero_of_not_mem_support U (by rw [hU]; simp [shape1])
  have h03 : U 0 3 = 0 := entry_eq_zero_of_not_mem_support U (by rw [hU]; simp [shape1])
  have h10 : U 1 0 = 0 := entry_eq_zero_of_not_mem_support U (by rw [hU]; simp [shape1])
  have h11 : U 1 1 = 0 := entry_eq_zero_of_not_mem_support U (by rw [hU]; simp [shape1])
  have h12 : U 1 2 = 0 := entry_eq_zero_of_not_mem_support U (by rw [hU]; simp [shape1])
  have h13 : U 1 3 = 0 := entry_eq_zero_of_not_mem_support U (by rw [hU]; simp [shape1])
  have h20 : U 2 0 = 0 := entry_eq_zero_of_not_mem_support U (by rw [hU]; simp [shape1])
  have h21 : U 2 1 = 0 := entry_eq_zero_of_not_mem_support U (by rw [hU]; simp [shape1])
  have h22 : U 2 2 = 0 := entry_eq_zero_of_not_mem_support U (by rw [hU]; simp [shape1])
  have h23 : U 2 3 = 0 := entry_eq_zero_of_not_mem_support U (by rw [hU]; simp [shape1])
  let a : ℚ := (U 0 0 : ℚ)
  have htotal : (matrixTotalNat U : ℚ) = a := by
    simp [a, matrixTotalNat, Fin.sum_univ_three, Fin.sum_univ_four,
      h01, h02, h03, h10, h11, h12, h13, h20, h21, h22, h23]
  have hF : a^2 ≤ matrixFNat U := by
    simp [a, matrixFNat, matrixOfNat, matrixF, rowSum, colSum,
      Fin.sum_univ_three, Fin.sum_univ_four,
      h01, h02, h03, h10, h11, h12, h13, h20, h21, h22, h23]
    nlinarith [sq_nonneg ((U 0 0 : ℚ))]
  exact matrix_theorem_of_one_component_star_bound U htotal le_rfl hF

/-- Canonical row-centered two-edge star case. -/
theorem canonical_shape2_row_minimum
    (U : NatMatrix) (hU : supportOfNat U = shape2_row) :
    matrixFNat U ≥ concreteM (matrixTotalNat U) := by
  have h02 : U 0 2 = 0 := entry_eq_zero_of_support_eq U hU (by simp [shape2_row])
  have h03 : U 0 3 = 0 := entry_eq_zero_of_support_eq U hU (by simp [shape2_row])
  have h10 : U 1 0 = 0 := entry_eq_zero_of_support_eq U hU (by simp [shape2_row])
  have h11 : U 1 1 = 0 := entry_eq_zero_of_support_eq U hU (by simp [shape2_row])
  have h12 : U 1 2 = 0 := entry_eq_zero_of_support_eq U hU (by simp [shape2_row])
  have h13 : U 1 3 = 0 := entry_eq_zero_of_support_eq U hU (by simp [shape2_row])
  have h20 : U 2 0 = 0 := entry_eq_zero_of_support_eq U hU (by simp [shape2_row])
  have h21 : U 2 1 = 0 := entry_eq_zero_of_support_eq U hU (by simp [shape2_row])
  have h22 : U 2 2 = 0 := entry_eq_zero_of_support_eq U hU (by simp [shape2_row])
  have h23 : U 2 3 = 0 := entry_eq_zero_of_support_eq U hU (by simp [shape2_row])
  let a : ℚ := (U 0 0 : ℚ)
  let b : ℚ := (U 0 1 : ℚ)
  have htotal : (matrixTotalNat U : ℚ) = a + b := by
    simp [a, b, matrixTotalNat, Fin.sum_univ_three, Fin.sum_univ_four,
      h02, h03, h10, h11, h12, h13, h20, h21, h22, h23]
  have hF : (a + b)^2 ≤ matrixFNat U := by
    simp [a, b, matrixFNat, matrixOfNat, matrixF, rowSum, colSum,
      Fin.sum_univ_three, Fin.sum_univ_four,
      h02, h03, h10, h11, h12, h13, h20, h21, h22, h23]
    nlinarith [sq_nonneg a, sq_nonneg b]
  exact matrix_theorem_of_one_component_star_bound U htotal le_rfl hF

/-- Canonical column-centered two-edge star case. -/
theorem canonical_shape2_col_minimum
    (U : NatMatrix) (hU : supportOfNat U = shape2_col) :
    matrixFNat U ≥ concreteM (matrixTotalNat U) := by
  have h01 : U 0 1 = 0 := entry_eq_zero_of_support_eq U hU (by simp [shape2_col])
  have h02 : U 0 2 = 0 := entry_eq_zero_of_support_eq U hU (by simp [shape2_col])
  have h03 : U 0 3 = 0 := entry_eq_zero_of_support_eq U hU (by simp [shape2_col])
  have h11 : U 1 1 = 0 := entry_eq_zero_of_support_eq U hU (by simp [shape2_col])
  have h12 : U 1 2 = 0 := entry_eq_zero_of_support_eq U hU (by simp [shape2_col])
  have h13 : U 1 3 = 0 := entry_eq_zero_of_support_eq U hU (by simp [shape2_col])
  have h20 : U 2 0 = 0 := entry_eq_zero_of_support_eq U hU (by simp [shape2_col])
  have h21 : U 2 1 = 0 := entry_eq_zero_of_support_eq U hU (by simp [shape2_col])
  have h22 : U 2 2 = 0 := entry_eq_zero_of_support_eq U hU (by simp [shape2_col])
  have h23 : U 2 3 = 0 := entry_eq_zero_of_support_eq U hU (by simp [shape2_col])
  let a : ℚ := (U 0 0 : ℚ)
  let b : ℚ := (U 1 0 : ℚ)
  have htotal : (matrixTotalNat U : ℚ) = a + b := by
    simp [a, b, matrixTotalNat, Fin.sum_univ_three, Fin.sum_univ_four,
      h01, h02, h03, h11, h12, h13, h20, h21, h22, h23]
  have hF : (a + b)^2 ≤ matrixFNat U := by
    simp [a, b, matrixFNat, matrixOfNat, matrixF, rowSum, colSum,
      Fin.sum_univ_three, Fin.sum_univ_four,
      h01, h02, h03, h11, h12, h13, h20, h21, h22, h23]
    nlinarith [sq_nonneg a, sq_nonneg b]
  exact matrix_theorem_of_one_component_star_bound U htotal le_rfl hF

/-- Canonical two singleton components case. -/
theorem canonical_shape2_singletons_minimum
    (U : NatMatrix) (hU : supportOfNat U = shape2_singletons) :
    matrixFNat U ≥ concreteM (matrixTotalNat U) := by
  have h01 : U 0 1 = 0 := entry_eq_zero_of_support_eq U hU (by simp [shape2_singletons])
  have h02 : U 0 2 = 0 := entry_eq_zero_of_support_eq U hU (by simp [shape2_singletons])
  have h03 : U 0 3 = 0 := entry_eq_zero_of_support_eq U hU (by simp [shape2_singletons])
  have h10 : U 1 0 = 0 := entry_eq_zero_of_support_eq U hU (by simp [shape2_singletons])
  have h12 : U 1 2 = 0 := entry_eq_zero_of_support_eq U hU (by simp [shape2_singletons])
  have h13 : U 1 3 = 0 := entry_eq_zero_of_support_eq U hU (by simp [shape2_singletons])
  have h20 : U 2 0 = 0 := entry_eq_zero_of_support_eq U hU (by simp [shape2_singletons])
  have h21 : U 2 1 = 0 := entry_eq_zero_of_support_eq U hU (by simp [shape2_singletons])
  have h22 : U 2 2 = 0 := entry_eq_zero_of_support_eq U hU (by simp [shape2_singletons])
  have h23 : U 2 3 = 0 := entry_eq_zero_of_support_eq U hU (by simp [shape2_singletons])
  let a : ℚ := (U 0 0 : ℚ)
  let b : ℚ := (U 1 1 : ℚ)
  have htotal : (matrixTotalNat U : ℚ) = a + b := by
    simp [a, b, matrixTotalNat, Fin.sum_univ_three, Fin.sum_univ_four,
      h01, h02, h03, h10, h12, h13, h20, h21, h22, h23]
  have hF : a^2 + b^2 ≤ matrixFNat U := by
    simp [a, b, matrixFNat, matrixOfNat, matrixF, rowSum, colSum,
      Fin.sum_univ_three, Fin.sum_univ_four,
      h01, h02, h03, h10, h12, h13, h20, h21, h22, h23]
    nlinarith [sq_nonneg a, sq_nonneg b]
  exact matrix_theorem_of_two_component_star_bound U htotal le_rfl le_rfl hF

/-- Three singleton star components give the manuscript's non-exceptional
three-component lower bound. -/
theorem matrix_theorem_of_three_singleton_star_bound
    (U : NatMatrix)
    {s₀ s₁ s₂ c₀ c₁ c₂ : ℚ}
    (htotal : (matrixTotalNat U : ℚ) = s₀ + s₁ + s₂)
    (hc₀ : (3 / 2 : ℚ) * s₀^2 ≤ c₀)
    (hc₁ : (3 / 2 : ℚ) * s₁^2 ≤ c₁)
    (hc₂ : (3 / 2 : ℚ) * s₂^2 ≤ c₂)
    (hF : c₀ + c₁ + c₂ ≤ matrixFNat U) :
    matrixFNat U ≥ concreteM (matrixTotalNat U) := by
  by_cases hsmall : matrixTotalNat U ≤ 3
  · exact matrix_theorem_of_total_le_three U hsmall
  · have hlarge : 4 ≤ matrixTotalNat U := by omega
    apply matrix_theorem_of_half_sq_bound_of_total_ge_four U hlarge
    rw [htotal]
    exact (three_singleton_component_half_bound hc₀ hc₁ hc₂).trans hF

/-- Exceptional `(2,1,1)` star forests reduce directly to the defining
integer quadruple minimum `M(n)`. -/
theorem matrix_theorem_of_exceptional_star_quad_bound
    (U : NatMatrix)
    {a b c d : ℕ}
    (htotal : matrixTotalNat U = a + b + c + d)
    (hF :
      quadCost (a : ℚ) (b : ℚ) (c : ℚ) (d : ℚ) ≤ matrixFNat U) :
    matrixFNat U ≥ concreteM (matrixTotalNat U) := by
  rw [htotal]
  exact (concreteM_le_quadCost_of_sum
    (a := a) (b := b) (c := c) (d := d) rfl).trans hF

end Lollipop

/-!
Proof component 3: `SectionFive.StarForestCases`.
The complete checked source follows; it is part of this numbered proof
module rather than an import from a generic project support directory.
-/

/-!
Completion of the finite star-forest support cases for Section 5.

The earlier matrix files define the sixteen canonical star-forest masks in
`K_{3,4}` and prove the first five directly.  This file keeps the remaining
case split in a separate namespace/folder so the final theorem-one assembly can
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

/-!
The manuscript-facing proposition is repeated here as `CoreStatement` so
this proof module does not cyclically import its public statement module.
`Statement.lean` imports this file and exposes the same expression under the
public name `Statement`.
-/

/-!
Manuscript Lemma 7.3 (`lem:starforest`): a star-forest support satisfies the
matrix lower bound.
-/

namespace Lollipop.Manuscript.Lemma_7_3

abbrev CoreStatement : Prop := StarForestMinimumStatement

end Lollipop.Manuscript.Lemma_7_3

/-! The actual numbered proof. -/

namespace Lollipop.Manuscript.Lemma_7_3

theorem proof : CoreStatement := by
  exact starForestMinimum_proven

end Lollipop.Manuscript.Lemma_7_3
