import Lollipop.Internal.Matrix.StarForest
import Lollipop.Internal.Matrix.Strategy
import Lollipop.Internal.MatrixAssembly.Dependencies

/-!
Theorem 1, organized as a formal dependency graph.

This module states the final theorem using mathlib's `IsGreatest` idiom and
proves it from named subtheorems.  In contrast with the earlier direct
certificate layer, the matrix component is a single global hypothesis
`MatrixTheoremStatement`; it is not repeated as a field of every quotient
certificate.
-/

namespace Lollipop
namespace TheoremOneFormal

universe u

/-- Pairwise upper certificates for every arrangement in a problem family,
with the Section 5 matrix theorem used globally rather than carried inside
each quotient certificate. -/
def PairwiseNatMatrixUpperCertificates (P : TheoremOne.ProblemFamily.{u}) :
    Prop :=
  ∀ n : ℕ, ∀ A : P.Arrangement n,
    ∃ L : PairwiseNatMatrixCertifiedLollipopUpper,
      L.nNat = n ∧ L.regions = P.region n A

/-- The three subtheorems needed for the formal Theorem 1 chain. -/
structure TheoremOneSubtheorems (P : TheoremOne.ProblemFamily.{u}) : Prop where
  matrix_theorem : MatrixTheoremStatement
  upper_certificates : PairwiseNatMatrixUpperCertificates P
  lower_realizations : TheoremOne.LowerRealizations P

/-- A more detailed version of the subtheorem package, exposing the two
Section 5 inputs that imply the matrix theorem. -/
structure DetailedTheoremOneSubtheorems
    (P : TheoremOne.ProblemFamily.{u}) : Prop where
  support_descent : SupportDescentStepStatement
  star_forest_minimum : StarForestMinimumStatement
  upper_certificates : PairwiseNatMatrixUpperCertificates P
  lower_realizations : TheoremOne.LowerRealizations P

/-- A Section 5 package reduced to the finite canonical star-forest cases. -/
structure CanonicalTheoremOneSubtheorems
    (P : TheoremOne.ProblemFamily.{u}) : Prop where
  support_descent : SupportDescentStepStatement
  canonical_star_forest_cases : CanonicalStarForestMinimumCases
  upper_certificates : PairwiseNatMatrixUpperCertificates P
  lower_realizations : TheoremOne.LowerRealizations P

/-- Collapse the detailed Section 5 package to the shorter subtheorem package
by proving the matrix theorem from descent and the star-forest minimum. -/
def DetailedTheoremOneSubtheorems.toTheoremOneSubtheorems
    {P : TheoremOne.ProblemFamily.{u}}
    (h : DetailedTheoremOneSubtheorems P) :
    TheoremOneSubtheorems P where
  matrix_theorem :=
    matrix_theorem_of_descent_step_and_star_forest
      h.support_descent h.star_forest_minimum
  upper_certificates := h.upper_certificates
  lower_realizations := h.lower_realizations

/-- Collapse the canonical Section 5 package to the shorter subtheorem package
by proving the matrix theorem from descent and the canonical star-forest
cases. -/
def CanonicalTheoremOneSubtheorems.toTheoremOneSubtheorems
    {P : TheoremOne.ProblemFamily.{u}}
    (h : CanonicalTheoremOneSubtheorems P) :
    TheoremOneSubtheorems P where
  matrix_theorem :=
    matrix_theorem_of_descent_step_and_canonical_cases
      h.support_descent h.canonical_star_forest_cases
  upper_certificates := h.upper_certificates
  lower_realizations := h.lower_realizations

/-- The upper-bound half of Theorem 1 from the matrix theorem and pairwise
integral-matrix upper certificates. -/
theorem upper_bound_of_pairwise_nat_matrix_certificates
    (P : TheoremOne.ProblemFamily.{u})
    (hMatrix : MatrixTheoremStatement)
    (hupper : PairwiseNatMatrixUpperCertificates P) :
    ∀ n : ℕ, ∀ A : P.Arrangement n,
      P.region n A ≤ candidateRegionsChoose n := by
  intro n A
  rcases hupper n A with ⟨L, hLn, hLreg⟩
  have hbound := pairwise_nat_matrix_certified_lollipop_upper_bound_choose hMatrix L
  rw [hLn] at hbound
  rw [← hLreg]
  exact hbound

/-- The lower-bound half is the previously checked lower-realization algebra,
converted to the displayed `Nat.choose` form. -/
theorem lower_attainment_of_realizations_choose
    (P : TheoremOne.ProblemFamily.{u})
    (hlower : TheoremOne.LowerRealizations P) :
    ∀ n : ℕ, ∃ A : P.Arrangement n,
      P.region n A = candidateRegionsChoose n := by
  intro n
  rcases TheoremOne.lower_attainment_of_realizations P hlower n with ⟨A, hA⟩
  exact ⟨A, by simpa [candidateRegionsChoose_eq_candidateRegions] using hA⟩

/-- Upper bound plus lower attainment imply the mathlib-style maximum
statement in the displayed formula form. -/
theorem maximumStatement_of_choose_upper_bound_and_lower_attainment
    (P : TheoremOne.ProblemFamily.{u})
    (hupper :
      ∀ n : ℕ, ∀ A : P.Arrangement n,
        P.region n A ≤ candidateRegionsChoose n)
    (hlower :
      ∀ n : ℕ, ∃ A : P.Arrangement n,
        P.region n A = candidateRegionsChoose n) :
    TheoremOne.MaximumStatement P := by
  intro n
  constructor
  · rcases hlower n with ⟨A, hA⟩
    exact ⟨A, hA⟩
  · intro y hy
    rcases hy with ⟨A, rfl⟩
    exact hupper n A

/-- Theorem 1 in maximum form from its named formal subtheorems. -/
theorem theorem_one_maximum_from_subtheorems
    (P : TheoremOne.ProblemFamily.{u})
    (h : TheoremOneSubtheorems P) :
    TheoremOne.MaximumStatement P := by
  exact maximumStatement_of_choose_upper_bound_and_lower_attainment P
    (upper_bound_of_pairwise_nat_matrix_certificates P
      h.matrix_theorem h.upper_certificates)
    (lower_attainment_of_realizations_choose P h.lower_realizations)

/-- Theorem 1 in maximum form from the detailed Section 5 subtheorems,
upper certificates, and lower realizations. -/
theorem theorem_one_maximum_from_detailed_subtheorems
    (P : TheoremOne.ProblemFamily.{u})
    (h : DetailedTheoremOneSubtheorems P) :
    TheoremOne.MaximumStatement P := by
  exact theorem_one_maximum_from_subtheorems P h.toTheoremOneSubtheorems

/-- Theorem 1 in maximum form from support descent, the finite canonical
star-forest cases, upper certificates, and lower realizations. -/
theorem theorem_one_maximum_from_canonical_subtheorems
    (P : TheoremOne.ProblemFamily.{u})
    (h : CanonicalTheoremOneSubtheorems P) :
    TheoremOne.MaximumStatement P := by
  exact theorem_one_maximum_from_subtheorems P h.toTheoremOneSubtheorems

/-- The same subtheorems for a family with a named maximum function. -/
def MaxTheoremOneSubtheorems (P : TheoremOne.MaxProblemFamily.{u}) : Prop :=
  TheoremOneSubtheorems P.toProblemFamily

/-- Detailed subtheorems for a family with a named maximum function. -/
def MaxDetailedTheoremOneSubtheorems
    (P : TheoremOne.MaxProblemFamily.{u}) : Prop :=
  DetailedTheoremOneSubtheorems P.toProblemFamily

/-- Canonical Section 5 subtheorems for a family with a named maximum
function. -/
def MaxCanonicalTheoremOneSubtheorems
    (P : TheoremOne.MaxProblemFamily.{u}) : Prop :=
  CanonicalTheoremOneSubtheorems P.toProblemFamily

/-- Theorem 1 in formula form for a named maximum-count function. -/
theorem theorem_one_formula_from_subtheorems
    (P : TheoremOne.MaxProblemFamily.{u})
    (h : MaxTheoremOneSubtheorems P) :
    TheoremOne.FormulaStatement P := by
  exact TheoremOne.formulaStatement_of_maximumStatement P
    (theorem_one_maximum_from_subtheorems P.toProblemFamily h)

/-- Theorem 1 in formula form from the detailed Section 5 subtheorems. -/
theorem theorem_one_formula_from_detailed_subtheorems
    (P : TheoremOne.MaxProblemFamily.{u})
    (h : MaxDetailedTheoremOneSubtheorems P) :
    TheoremOne.FormulaStatement P := by
  exact TheoremOne.formulaStatement_of_maximumStatement P
    (theorem_one_maximum_from_detailed_subtheorems P.toProblemFamily h)

/-- Theorem 1 in formula form from support descent and the finite canonical
star-forest cases. -/
theorem theorem_one_formula_from_canonical_subtheorems
    (P : TheoremOne.MaxProblemFamily.{u})
    (h : MaxCanonicalTheoremOneSubtheorems P) :
    TheoremOne.FormulaStatement P := by
  exact TheoremOne.formulaStatement_of_maximumStatement P
    (theorem_one_maximum_from_canonical_subtheorems P.toProblemFamily h)

/-- Single-size formula statement for Theorem 1. -/
theorem theorem_one_formula_at_from_subtheorems
    (P : TheoremOne.MaxProblemFamily.{u})
    (h : MaxTheoremOneSubtheorems P)
    (n : ℕ) :
    P.aLop n =
      4 * ((n.choose 2 : ℕ) : ℚ) + concreteS n + (n : ℚ) + 1 := by
  exact theorem_one_formula_from_subtheorems P h n

/-- Single-size formula statement from the detailed Section 5 subtheorems. -/
theorem theorem_one_formula_at_from_detailed_subtheorems
    (P : TheoremOne.MaxProblemFamily.{u})
    (h : MaxDetailedTheoremOneSubtheorems P)
    (n : ℕ) :
    P.aLop n =
      4 * ((n.choose 2 : ℕ) : ℚ) + concreteS n + (n : ℚ) + 1 := by
  exact theorem_one_formula_from_detailed_subtheorems P h n

/-- Single-size formula statement from support descent and the finite
canonical star-forest cases. -/
theorem theorem_one_formula_at_from_canonical_subtheorems
    (P : TheoremOne.MaxProblemFamily.{u})
    (h : MaxCanonicalTheoremOneSubtheorems P)
    (n : ℕ) :
    P.aLop n =
      4 * ((n.choose 2 : ℕ) : ℚ) + concreteS n + (n : ℚ) + 1 := by
  exact theorem_one_formula_from_canonical_subtheorems P h n

end TheoremOneFormal
end Lollipop
