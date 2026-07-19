import Lollipop.Lemma_3_1.Proof

/-!
This is the substantive proof compilation unit for `Proposition_3_3`.
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
Manuscript Proposition 3.3 (`prop:pair-savings`): the universal, close,
intriguing, and combined close/intriguing pair-excess bounds.
-/

namespace Lollipop.Manuscript.Proposition_3_3

open Concrete Concrete.EndToEnd

def CoreStatement : Prop :=
  forall (L M : Concrete.Lollipop),
    pairExcess L M <= 7 /\
    (PairGeometry.Close L M -> pairExcess L M <= 5) /\
    (PairGeometry.Intriguing L M -> pairExcess L M <= 5) /\
    (PairGeometry.Close L M -> PairGeometry.Intriguing L M ->
      pairExcess L M <= 4)

end Lollipop.Manuscript.Proposition_3_3

/-! The actual numbered proof. -/

namespace Lollipop.Manuscript.Proposition_3_3

open Concrete Concrete.EndToEnd Concrete.EndToEnd.PairGeometry

theorem proof : CoreStatement := by
  intro L M
  exact ⟨pairExcess_le_seven L M,
    fun h => pairExcess_le_five_of_close h,
    fun h => pairExcess_le_five_of_intriguing h,
    fun hc hi => pairExcess_le_four_of_close_intriguing hc hi⟩

end Lollipop.Manuscript.Proposition_3_3
