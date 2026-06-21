import Lollipop.Internal.SectionFive.SupportDescent
import Lollipop.Internal.MatrixAssembly.Proof

/-!
Theorem 1 assembly with Section 5 discharged.

This file is the manuscript-facing final dependency package.  Unlike
`TheoremOneFormal.Proof`, it no longer asks for the matrix theorem, support
descent, or star-forest minimum as inputs: those are proved in
`TheoremOneComplete.SupportDescent` and imported here.  The remaining inputs
are the problem-family upper certificates and lower realizations, which encode
the external geometric/construction data for the chosen lollipop model.
-/

namespace Lollipop
namespace TheoremOneComplete

universe u

/-- The remaining non-Section-5 inputs needed for Theorem 1 over an abstract
problem family.  Section 5's matrix theorem is now supplied by
`matrix_theorem_proven`. -/
structure TheoremOneInputs (P : TheoremOne.ProblemFamily.{u}) : Prop where
  upper_certificates : TheoremOneFormal.PairwiseNatMatrixUpperCertificates P
  lower_realizations : TheoremOne.LowerRealizations P

/-- Convert the complete-input package to the older formal subtheorem package
by filling the matrix field with the checked Section 5 theorem. -/
def TheoremOneInputs.toFormalSubtheorems
    {P : TheoremOne.ProblemFamily.{u}}
    (h : TheoremOneInputs P) :
    TheoremOneFormal.TheoremOneSubtheorems P where
  matrix_theorem := matrix_theorem_proven
  upper_certificates := h.upper_certificates
  lower_realizations := h.lower_realizations

/-- Theorem 1 in maximum form with the matrix theorem fully discharged. -/
theorem theorem_one_maximum
    (P : TheoremOne.ProblemFamily.{u})
    (h : TheoremOneInputs P) :
    TheoremOne.MaximumStatement P := by
  exact TheoremOneFormal.theorem_one_maximum_from_subtheorems P
    h.toFormalSubtheorems

/-- Complete inputs for a family with a named maximum-count function. -/
def MaxTheoremOneInputs (P : TheoremOne.MaxProblemFamily.{u}) : Prop :=
  TheoremOneInputs P.toProblemFamily

/-- Theorem 1 in formula form with the matrix theorem fully discharged. -/
theorem theorem_one_formula
    (P : TheoremOne.MaxProblemFamily.{u})
    (h : MaxTheoremOneInputs P) :
    TheoremOne.FormulaStatement P := by
  exact TheoremOne.formulaStatement_of_maximumStatement P
    (theorem_one_maximum P.toProblemFamily h)

/-- Single-size displayed formula for Theorem 1. -/
theorem theorem_one_formula_at
    (P : TheoremOne.MaxProblemFamily.{u})
    (h : MaxTheoremOneInputs P)
    (n : Nat) :
    P.aLop n =
      4 * ((n.choose 2 : Nat) : Rat) + concreteS n + (n : Rat) + 1 := by
  exact theorem_one_formula P h n

end TheoremOneComplete
end Lollipop
