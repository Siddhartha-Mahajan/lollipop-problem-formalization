import Lollipop.Lemma_8_5.Proof

/-!
This is the substantive proof compilation unit for `Theorem_1_1`.
All project proof components used below are integrated here or imported
directly from another manuscript-numbered `Proof.lean` file.
-/

/-!
The manuscript-facing proposition is repeated here as `CoreStatement` so
this proof module does not cyclically import its public statement module.
`Statement.lean` imports this file and exposes the same expression under the
public name `Statement`.
-/

/-!
Manuscript Theorem 1.1 (`thm:main`): for every `n`, the maximum number of
regions is `4 * choose n 2 + S(n) + n + 1`.
-/

namespace Lollipop.Manuscript.Theorem_1_1

universe u

abbrev CoreStatement (P : TheoremOne.MaxProblemFamily.{u}) : Prop :=
  TheoremOneManuscript.FormalizedProof.FinalTheoremOneStatement P

end Lollipop.Manuscript.Theorem_1_1

/-! The actual numbered proof. -/

namespace Lollipop.Manuscript.Theorem_1_1

universe u

/-- Checked assembly of Theorem 1.1 from the manuscript-scale upper-geometry
and Karlsson lower-construction subtheorems. -/
theorem proof
    (P : TheoremOne.MaxProblemFamily.{u})
    (h : TheoremOneManuscript.FormalizedProof.StrongestKnownTheoremOneSubtheorems P) :
    CoreStatement P := by
  exact
    TheoremOneManuscript.FormalizedProof.theorem_one_from_formalized_subtheorems
      P h

end Lollipop.Manuscript.Theorem_1_1
