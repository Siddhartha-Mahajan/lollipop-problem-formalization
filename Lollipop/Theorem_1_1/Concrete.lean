import Lollipop.Theorem_1_1.Proof
import Lollipop.Topology.ConcreteMaximum

/-!
Manuscript Theorem 1.1 (`thm:main`), concrete form: for every `n`, the
maximum number of complementary regions of `n` Euclidean lollipops is
`4 * choose n 2 + S(n) + n + 1`.  The lollipops, their carriers and the
region count (connected components of the complement of the union of
carriers) are the concrete Lean definitions of `Lollipop.Concrete`; nothing is
assumed.
-/

namespace Lollipop.Manuscript.Theorem_1_1

open Concrete Concrete.EndToEnd

/-- The concrete statement of Theorem 1.1. -/
def ConcreteStatement : Prop :=
  ∀ n : ℕ,
    IsGreatest
      (Set.range (fun A : Arrangement n => (regionCount A : ℚ)))
      (4 * ((n.choose 2 : ℕ) : ℚ) + TheoremOneManuscript.manuscriptS n + (n : ℚ) + 1)

/-- Theorem 1.1, with no hypotheses (the numbered proof endpoint). -/
theorem proof : ConcreteStatement :=
  fun n => MainTheorem.Final.lollipopMaximum_expanded n

end Lollipop.Manuscript.Theorem_1_1
