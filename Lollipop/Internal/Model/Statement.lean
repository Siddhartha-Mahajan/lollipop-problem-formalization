import Lollipop.Internal.Core

/-!
Top-level statements for Theorem 1.

Mathlib's `IsGreatest` is the right shape for a maximum theorem over an
abstract arrangement class: it simultaneously states that the displayed value
is attained and that every arrangement has region count at most that value.
This avoids introducing a noncomputable supremum over `ℚ`.
-/

namespace Lollipop
namespace TheoremOne

universe u

/-- An abstract family of lollipop arrangements, indexed by the number of
lollipops, together with its region-count function. -/
structure ProblemFamily where
  Arrangement : ℕ → Type u
  region : (n : ℕ) → Arrangement n → ℚ

/-- The set of region counts attained by arrangements of size `n`. -/
def regionSet (P : ProblemFamily.{u}) (n : ℕ) : Set ℚ :=
  Set.range (P.region n)

/-- Theorem 1 in maximum form:
`4 * n.choose 2 + S(n) + n + 1` is the greatest attained region count. -/
def MaximumStatement (P : ProblemFamily.{u}) : Prop :=
  ∀ n : ℕ, IsGreatest (regionSet P n) (candidateRegionsChoose n)

/-- A problem family with a named maximum-count function `aLop`.  The field
`aLop_spec` is the mathematical meaning of that name: it is the greatest
attained region count. -/
structure MaxProblemFamily where
  Arrangement : ℕ → Type u
  region : (n : ℕ) → Arrangement n → ℚ
  aLop : ℕ → ℚ
  aLop_spec : ∀ n : ℕ, IsGreatest (Set.range (region n)) (aLop n)

/-- Forget the named maximum-count function. -/
def MaxProblemFamily.toProblemFamily (P : MaxProblemFamily.{u}) : ProblemFamily.{u} where
  Arrangement := P.Arrangement
  region := P.region

/-- Theorem 1 in formula form for a named maximum-count function. -/
def FormulaStatement (P : MaxProblemFamily.{u}) : Prop :=
  ∀ n : ℕ, P.aLop n = candidateRegionsChoose n

/-- If the candidate value is greatest, then any named maximum-count function
with an `IsGreatest` specification is equal to the candidate formula. -/
theorem formulaStatement_of_maximumStatement
    (P : MaxProblemFamily.{u})
    (hmax : MaximumStatement P.toProblemFamily) :
    FormulaStatement P := by
  intro n
  exact (P.aLop_spec n).unique (hmax n)

end TheoremOne
end Lollipop
