import Lollipop.Lemma_7_2.Proof
import Lollipop.Lemma_7_3.Proof

/-!
Substantive proof of manuscript Theorem 7.1.  Lemma 7.2 supplies the
checked support-descent step and Lemma 7.3 supplies the checked minimum on
star-forest supports.  This file performs the final well-founded descent
assembly explicitly.
-/

namespace Lollipop

/-- The full matrix theorem, assembled from its two numbered lemmas. -/
theorem matrix_theorem_proven : MatrixTheoremStatement :=
  matrix_theorem_of_descent_step_and_star_forest
    support_descent_step_proven starForestMinimum_proven

end Lollipop

namespace Lollipop.Manuscript.Theorem_7_1

abbrev CoreStatement : Prop := MatrixTheoremStatement

/-- The checked proof of the manuscript-numbered matrix theorem. -/
theorem proof : CoreStatement := by
  exact Lollipop.matrix_theorem_proven

end Lollipop.Manuscript.Theorem_7_1
