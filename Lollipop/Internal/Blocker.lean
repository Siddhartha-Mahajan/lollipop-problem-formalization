import Lollipop.Internal.Algebra
import Mathlib.Tactic

/-!
Checked algebra for the weighted blocker step.

This file formalizes the numerical chain in manuscript Section 4:

* weighted Turan lower bounds for the two blocker graphs,
* the comparison between the original weight-square sum `Q` and the
  `3 x 4` intersection-matrix square sum,
* the matrix-theorem lower bound.

The graph-theoretic existence of the weighted Turan partitions and the matrix
theorem itself are deliberately hypotheses here; the inequalities connecting
them are machine checked.
-/

namespace Lollipop

/-- The blocker cost appearing in the colored Turan quotient. -/
def blockerCost (Q a b : ℚ) : ℚ :=
  (3 / 2 : ℚ) * Q + 2 * a + 2 * b

/-- The matrix side obtained after intersecting a minimizing 3-partition and
a minimizing 4-partition. -/
def partitionMatrixSide (rho3 rho4 entrySq : ℚ) : ℚ :=
  rho3 + rho4 - (1 / 2 : ℚ) * entrySq

/-- The purely algebraic core of the weighted blocker lemma. -/
theorem blocker_cost_ge_partition_side
    {Q a b rho3 rho4 entrySq : ℚ}
    (ha : a ≥ (rho3 - Q) / 2)
    (hb : b ≥ (rho4 - Q) / 2)
    (hQ : Q ≤ entrySq) :
    blockerCost Q a b ≥ partitionMatrixSide rho3 rho4 entrySq := by
  unfold blockerCost partitionMatrixSide
  nlinarith

/-- If the matrix side is at least `M`, then the blocker cost is at least
`M`.  This is exactly the last inequality chain in Lemma 5 of the manuscript. -/
theorem blocker_cost_ge_of_matrix_bound
    {Q a b rho3 rho4 entrySq M : ℚ}
    (ha : a ≥ (rho3 - Q) / 2)
    (hb : b ≥ (rho4 - Q) / 2)
    (hQ : Q ≤ entrySq)
    (hmatrix : partitionMatrixSide rho3 rho4 entrySq ≥ M) :
    blockerCost Q a b ≥ M := by
  have hside : blockerCost Q a b ≥ partitionMatrixSide rho3 rho4 entrySq :=
    blocker_cost_ge_partition_side ha hb hQ
  exact ge_trans hside hmatrix

/-- Same result in the notational shape used by `Core.lean`. -/
theorem blocker_cost_ge_M
    {Q a b rho3 rho4 entrySq M : ℚ}
    (ha : a ≥ (rho3 - Q) / 2)
    (hb : b ≥ (rho4 - Q) / 2)
    (hQ : Q ≤ entrySq)
    (hmatrix :
      rho3 + rho4 - (1 / 2 : ℚ) * entrySq ≥ M) :
    (3 / 2 : ℚ) * Q + 2 * a + 2 * b ≥ M := by
  exact blocker_cost_ge_of_matrix_bound ha hb hQ hmatrix

/-- The scalar `partitionMatrixSide` is exactly `matrixF` when its arguments
are supplied by the row-square, column-square, and entry-square sums of `U`. -/
theorem partitionMatrixSide_eq_matrixF (U : Fin 3 → Fin 4 → ℚ) :
    partitionMatrixSide
      (∑ i : Fin 3, (rowSum U i)^2)
      (∑ j : Fin 4, (colSum U j)^2)
      (∑ i : Fin 3, ∑ j : Fin 4, (U i j)^2) =
      matrixF U := by
  rfl

/-- Blocker conclusion using an explicit `3 x 4` matrix bound. -/
theorem blocker_cost_ge_of_matrixF_bound
    {Q a b rho3 rho4 entrySq M : ℚ}
    (U : Fin 3 → Fin 4 → ℚ)
    (ha : a ≥ (rho3 - Q) / 2)
    (hb : b ≥ (rho4 - Q) / 2)
    (hQ : Q ≤ entrySq)
    (hrho3 : rho3 = ∑ i : Fin 3, (rowSum U i)^2)
    (hrho4 : rho4 = ∑ j : Fin 4, (colSum U j)^2)
    (hentry : entrySq = ∑ i : Fin 3, ∑ j : Fin 4, (U i j)^2)
    (hmatrix : matrixF U ≥ M) :
    blockerCost Q a b ≥ M := by
  apply blocker_cost_ge_of_matrix_bound ha hb hQ
  rw [hrho3, hrho4, hentry, partitionMatrixSide_eq_matrixF]
  exact hmatrix

/-- Algebra behind the quotient objective identity
`sigma = 3P - 2a - 2b = 3/2 (n^2 - Q) - 2a - 2b`. -/
theorem quotient_identity_from_cross_mass
    {n Q P a b sigma : ℚ}
    (hP : P = (n^2 - Q) / 2)
    (hsigma : sigma = 3 * P - 2 * a - 2 * b) :
    sigma =
      (3 / 2 : ℚ) * n^2 - ((3 / 2 : ℚ) * Q + 2 * a + 2 * b) := by
  rw [hsigma, hP]
  ring

end Lollipop
