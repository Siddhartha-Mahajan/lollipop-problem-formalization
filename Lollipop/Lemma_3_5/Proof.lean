import Lollipop.Lemma_3_1.Proof

/-!
This is the substantive proof compilation unit for `Lemma_3_5`.
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
Manuscript Lemma 3.5 (`lem:forced-intriguing`): every five circles contain an
intriguing pair.
-/

namespace Lollipop.Manuscript.Lemma_3_5

open Concrete Concrete.EndToEnd

def CoreStatement : Prop :=
  forall {n : Nat} (A : Arrangement n) (t : Finset (Fin n)), t.card = 5 ->
    ∃ i ∈ t, ∃ j ∈ t,
      i ≠ j /\ PairGeometry.Intriguing (A i) (A j)

end Lollipop.Manuscript.Lemma_3_5

/-! The actual numbered proof. -/

namespace Lollipop.Manuscript.Lemma_3_5

open Concrete Concrete.EndToEnd

theorem proof : CoreStatement := by
  intro n A t ht
  exact PairGeometry.intriguing_pair_in_every_five A t ht

end Lollipop.Manuscript.Lemma_3_5
