import Lollipop.Internal.ColoredTuran.PartitionCertificates
import Lollipop.Internal.SectionFive.Proof

/-!
Theorem 1 as a final Lean statement from proved subtheorems.

This is the most expanded theorem assembly in the repository.  The matrix
theorem, all Section 5 compression cases, finite-sum crossing reduction,
lower-construction algebra, and partition-intersection matrix algebra are
proved in imported files.  The input package below contains only the
certificate-producing statements for the actual lollipop model.
-/

namespace Lollipop
namespace TheoremOneEndToEnd

universe u

/-- The remaining model-specific inputs after the generic proof has been
formalized.  These are certificate-production statements: for every lollipop
arrangement, produce the pairwise/colored/weighted quotient certificate, and
for every admissible four-cluster lower pattern, produce a realizing
arrangement. -/
structure TheoremOneSubtheorems (P : TheoremOne.ProblemFamily.{u}) : Prop where
  upper_certificates : PairwisePartitionMatrixUpperCertificates P
  lower_realizations : TheoremOne.LowerRealizations P

/-- Convert the refined end-to-end package to the complete package where the
matrix theorem has already been discharged. -/
def TheoremOneSubtheorems.toCompleteInputs
    {P : TheoremOne.ProblemFamily.{u}}
    (h : TheoremOneSubtheorems P) :
    TheoremOneComplete.TheoremOneInputs P where
  upper_certificates :=
    pairwise_partition_matrix_upper_certificates_to_nat_matrix h.upper_certificates
  lower_realizations := h.lower_realizations

/-- Theorem 1 in maximum form, with all generic algebraic and matrix
subtheorems proved and only model-specific certificate production supplied. -/
theorem theorem_one_maximum
    (P : TheoremOne.ProblemFamily.{u})
    (h : TheoremOneSubtheorems P) :
    TheoremOne.MaximumStatement P := by
  exact TheoremOneComplete.theorem_one_maximum P h.toCompleteInputs

/-- End-to-end inputs for a problem family with a named maximum-count
function. -/
def MaxTheoremOneSubtheorems (P : TheoremOne.MaxProblemFamily.{u}) : Prop :=
  TheoremOneSubtheorems P.toProblemFamily

/-- Theorem 1 in the manuscript formula form for a named maximum-count
function. -/
theorem theorem_one_formula
    (P : TheoremOne.MaxProblemFamily.{u})
    (h : MaxTheoremOneSubtheorems P) :
    TheoremOne.FormulaStatement P := by
  exact TheoremOne.formulaStatement_of_maximumStatement P
    (theorem_one_maximum P.toProblemFamily h)

/-- Single-size version of Theorem 1 in the displayed manuscript form. -/
theorem theorem_one_formula_at
    (P : TheoremOne.MaxProblemFamily.{u})
    (h : MaxTheoremOneSubtheorems P)
    (n : Nat) :
    P.aLop n =
      4 * ((n.choose 2 : Nat) : Rat) + concreteS n + (n : Rat) + 1 := by
  exact theorem_one_formula P h n

end TheoremOneEndToEnd
end Lollipop
