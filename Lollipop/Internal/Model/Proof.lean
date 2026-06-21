import Lollipop.Internal.Model.Statement
import Lollipop.Internal.Upper

/-!
Proof of the Theorem 1 statement from the certified subtheorems.

This file is intentionally only an orchestration layer.  The algebraic and
combinatorial work is proved in the imported modules; the remaining external
inputs are explicit certificate-producing hypotheses.
-/

namespace Lollipop
namespace TheoremOne

universe u

/-- Pairwise direct upper certificates for every arrangement in a problem
family.  This packages the geometric pointwise estimates, two-graph reduction,
colored quotient certificate, weighted blocker inputs, and matrix certificate
for each arrangement. -/
def PairwiseDirectUpperCertificates (P : ProblemFamily.{u}) : Prop :=
  ∀ n : ℕ, ∀ A : P.Arrangement n,
    ∃ L : PairwiseDirectCertifiedLollipopUpper,
      L.nNat = n ∧ L.regions = P.region n A

/-- Lower realization for every size in a problem family. -/
def LowerRealizations (P : ProblemFamily.{u}) : Prop :=
  ∀ n : ℕ, LowerRealization (P.Arrangement n) (P.region n) n

/-- Lower crossing-count realization for every size in a problem family.  The
extra function records the crossing count of each lower-construction
arrangement; Lean then uses `regions = crossings + n + 1` to recover the older
lower-realization interface. -/
def LowerCrossingRealizations
    (P : ProblemFamily.{u})
    (crossings : (n : ℕ) → P.Arrangement n → ℚ) : Prop :=
  ∀ n : ℕ,
    LowerCrossingRealization (P.Arrangement n) (P.region n) (crossings n) n

/-- Crossing-count lower realizations imply the older region-count lower
realizations. -/
theorem lowerRealizations_of_lowerCrossingRealizations
    (P : ProblemFamily.{u})
    {crossings : (n : ℕ) → P.Arrangement n → ℚ}
    (hlower : LowerCrossingRealizations P crossings) :
    LowerRealizations P := by
  intro n
  exact lowerRealization_of_lowerCrossingRealization (hlower n)

/-- The upper-bound half of Theorem 1, derived from pairwise direct
certificates. -/
theorem upper_bound_of_pairwise_direct_certificates
    (P : ProblemFamily.{u})
    (hupper : PairwiseDirectUpperCertificates P) :
    ∀ n : ℕ, ∀ A : P.Arrangement n,
      P.region n A ≤ candidateRegionsChoose n := by
  intro n A
  rcases hupper n A with ⟨L, hLn, hLreg⟩
  have hbound := pairwise_direct_certified_lollipop_upper_bound_choose L
  rw [hLn] at hbound
  rw [← hLreg]
  exact hbound

/-- The lower-bound half of Theorem 1, derived from the lower-realization
hypothesis and the finite maximizer of `concreteS n`. -/
theorem lower_attainment_of_realizations
    (P : ProblemFamily.{u})
    (hlower : LowerRealizations P) :
    ∀ n : ℕ, ∃ A : P.Arrangement n,
      P.region n A = candidateRegionsChoose n := by
  intro n
  rcases exists_region_eq_candidate_of_lowerRealization
      (Arrangement := P.Arrangement n) (region := P.region n)
      (n := n) (hlower n) with ⟨A, hA⟩
  exact ⟨A, by simpa [candidateRegionsChoose_eq_candidateRegions] using hA⟩

/-- Upper bound plus lower attainment imply the maximum statement. -/
theorem maximumStatement_of_upper_bound_and_lower_attainment
    (P : ProblemFamily.{u})
    (hupper :
      ∀ n : ℕ, ∀ A : P.Arrangement n,
        P.region n A ≤ candidateRegionsChoose n)
    (hlower :
      ∀ n : ℕ, ∃ A : P.Arrangement n,
        P.region n A = candidateRegionsChoose n) :
    MaximumStatement P := by
  intro n
  constructor
  · rcases hlower n with ⟨A, hA⟩
    exact ⟨A, hA⟩
  · intro y hy
    rcases hy with ⟨A, rfl⟩
    exact hupper n A

/-- Theorem 1 in maximum form, proved from pairwise direct upper certificates
and lower realizations. -/
theorem theorem_one_maximum_from_pairwise_direct_certificates
    (P : ProblemFamily.{u})
    (hupper : PairwiseDirectUpperCertificates P)
    (hlower : LowerRealizations P) :
    MaximumStatement P := by
  exact maximumStatement_of_upper_bound_and_lower_attainment P
    (upper_bound_of_pairwise_direct_certificates P hupper)
    (lower_attainment_of_realizations P hlower)

/-- Pairwise direct upper certificates for a family with a named maximum
function. -/
def MaxPairwiseDirectUpperCertificates (P : MaxProblemFamily.{u}) : Prop :=
  PairwiseDirectUpperCertificates P.toProblemFamily

/-- Lower realizations for a family with a named maximum function. -/
def MaxLowerRealizations (P : MaxProblemFamily.{u}) : Prop :=
  LowerRealizations P.toProblemFamily

/-- Theorem 1 in formula form:
`a_Lop(n) = 4 * n.choose 2 + S(n) + n + 1`, proved from pairwise direct upper
certificates and lower realizations. -/
theorem theorem_one_formula_from_pairwise_direct_certificates
    (P : MaxProblemFamily.{u})
    (hupper : MaxPairwiseDirectUpperCertificates P)
    (hlower : MaxLowerRealizations P) :
    FormulaStatement P := by
  apply formulaStatement_of_maximumStatement
  exact theorem_one_maximum_from_pairwise_direct_certificates
    P.toProblemFamily hupper hlower

/-- A single-size version of Theorem 1 in formula form. -/
theorem theorem_one_formula_at
    (P : MaxProblemFamily.{u})
    (hupper : MaxPairwiseDirectUpperCertificates P)
    (hlower : MaxLowerRealizations P)
    (n : ℕ) :
    P.aLop n =
      4 * ((n.choose 2 : ℕ) : ℚ) + concreteS n + (n : ℚ) + 1 := by
  exact theorem_one_formula_from_pairwise_direct_certificates P hupper hlower n

end TheoremOne
end Lollipop
