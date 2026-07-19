import Lollipop.Theorem_1_1.Proof

/-!
Manuscript Theorem 1.1 (`thm:main`): for every `n`, the maximum number of
regions is `4 * choose n 2 + S(n) + n + 1`.
-/

namespace Lollipop.Manuscript.Theorem_1_1

universe u

abbrev Statement (P : TheoremOne.MaxProblemFamily.{u}) : Prop :=
  TheoremOneManuscript.FormalizedProof.FinalTheoremOneStatement P

end Lollipop.Manuscript.Theorem_1_1
