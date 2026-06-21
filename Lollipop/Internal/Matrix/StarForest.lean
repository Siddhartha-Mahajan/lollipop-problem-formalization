import Lollipop.Internal.CompressionAlgebra
import Lollipop.Internal.Matrix.Shapes
import Lollipop.Internal.Matrix.Strategy

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
