import Lollipop.Internal.Matrix.Support

/-!
Section 5 proof strategy.

This module records the exact dependency split of the manuscript's matrix
theorem.  The two remaining global ingredients are:

* support compression to star-forest normal form without increasing `F`;
* the lower bound for matrices already in star-forest normal form.

Once those two statements are proved, `MatrixTheoremStatement` follows by a
short checked argument.
-/

namespace Lollipop

/-- Manuscript Lemma 5.1: support compression to star-forest normal form. -/
def SupportCompressionStatement : Prop :=
  ∀ U : NatMatrix,
    ∃ V : NatMatrix,
      matrixTotalNat V = matrixTotalNat U ∧
      matrixFNat V ≤ matrixFNat U ∧
      IsSupportStarForest (supportOfNat V)

/-- Manuscript Lemma 5.2: the matrix bound on star-forest supports. -/
def StarForestMinimumStatement : Prop :=
  ∀ U : NatMatrix,
    IsSupportStarForest (supportOfNat U) →
      matrixFNat U ≥ concreteM (matrixTotalNat U)

/-- A one-step descent statement: every non-star support has a total-preserving
move that does not increase `F` and strictly decreases support cardinality. -/
def SupportDescentStepStatement : Prop :=
  ∀ U : NatMatrix,
    ¬ IsSupportStarForest (supportOfNat U) →
      ∃ V : NatMatrix,
        matrixTotalNat V = matrixTotalNat U ∧
        matrixFNat V ≤ matrixFNat U ∧
        supportCardNat V < supportCardNat U

/-- A checked termination argument for support compression.  Thus the global
iteration in the manuscript reduces to the one-step descent lemma. -/
theorem support_compression_of_descent_step
    (hstep : SupportDescentStepStatement) :
    SupportCompressionStatement := by
  intro U
  let C : NatMatrix → Prop := fun U =>
    ∃ V : NatMatrix,
      matrixTotalNat V = matrixTotalNat U ∧
      matrixFNat V ≤ matrixFNat U ∧
      IsSupportStarForest (supportOfNat V)
  change C U
  refine (measure supportCardNat).wf.induction U ?_
  intro U ih
  by_cases hstar : IsSupportStarForest (supportOfNat U)
  · exact ⟨U, rfl, le_rfl, hstar⟩
  · rcases hstep U hstar with ⟨V, htotal, hF, hcard⟩
    rcases ih V hcard with ⟨W, hWtotal, hWF, hWstar⟩
    refine ⟨W, ?_, ?_, hWstar⟩
    · rw [hWtotal, htotal]
    · linarith

/-- The Section 5 matrix theorem follows from support compression and the
star-forest minimum. -/
theorem matrix_theorem_of_support_compression_and_star_forest
    (hcompress : SupportCompressionStatement)
    (hstar : StarForestMinimumStatement) :
    MatrixTheoremStatement := by
  intro U
  rcases hcompress U with ⟨V, htotal, hF, hVstar⟩
  have hV := hstar V hVstar
  rw [htotal] at hV
  linarith

/-- The matrix theorem follows from one-step descent plus the star-forest
minimum. -/
theorem matrix_theorem_of_descent_step_and_star_forest
    (hstep : SupportDescentStepStatement)
    (hstar : StarForestMinimumStatement) :
    MatrixTheoremStatement := by
  exact matrix_theorem_of_support_compression_and_star_forest
    (support_compression_of_descent_step hstep) hstar

/-- For total mass at least four, the manuscript's non-exceptional
star-forest estimate `F(U) >= n^2 / 2` is enough. -/
theorem matrix_theorem_of_half_sq_bound_of_total_ge_four
    (U : NatMatrix)
    (hlarge : 4 ≤ matrixTotalNat U)
    (hhalf : (matrixTotalNat U : ℚ)^2 / 2 ≤ matrixFNat U) :
    matrixFNat U ≥ concreteM (matrixTotalNat U) := by
  have hM := concreteM_le_half_sq_of_ge_four
    (n := matrixTotalNat U) hlarge
  linarith

/-- A combined branch lemma for the star-forest proof: either the total is
small, or the `n^2 / 2` estimate is enough. -/
theorem matrix_theorem_of_small_or_half_sq_bound
    (U : NatMatrix)
    (hbranch :
      matrixTotalNat U ≤ 3 ∨
        4 ≤ matrixTotalNat U ∧
          (matrixTotalNat U : ℚ)^2 / 2 ≤ matrixFNat U) :
    matrixFNat U ≥ concreteM (matrixTotalNat U) := by
  rcases hbranch with hsmall | hlarge
  · exact matrix_theorem_of_total_le_three U hsmall
  · exact matrix_theorem_of_half_sq_bound_of_total_ge_four U
      hlarge.1 hlarge.2

end Lollipop
