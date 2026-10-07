import Lollipop.Theorem_1_1.Concrete

/-!
Manuscript Theorem 1.1 (`thm:main`): for every `n`, the maximum number of
regions is `4 * choose n 2 + S(n) + n + 1`.
-/

namespace Lollipop.Manuscript.Theorem_1_1

universe u

/-- The manuscript-facing statement: concrete Euclidean lollipops. -/
abbrev Statement : Prop := ConcreteStatement

/-- The abstract-problem-family form assembled from the subtheorem package. -/
abbrev AbstractStatement (P : TheoremOne.MaxProblemFamily.{u}) : Prop :=
  TheoremOneManuscript.FormalizedProof.FinalTheoremOneStatement P

end Lollipop.Manuscript.Theorem_1_1
