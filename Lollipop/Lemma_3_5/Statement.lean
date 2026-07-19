import Lollipop.Lemma_3_5.Proof

/-!
Manuscript Lemma 3.5 (`lem:forced-intriguing`): every five circles contain an
intriguing pair.
-/

namespace Lollipop.Manuscript.Lemma_3_5

open Concrete Concrete.EndToEnd

def Statement : Prop :=
  forall {n : Nat} (A : Arrangement n) (t : Finset (Fin n)), t.card = 5 ->
    ∃ i ∈ t, ∃ j ∈ t,
      i ≠ j /\ PairGeometry.Intriguing (A i) (A j)

end Lollipop.Manuscript.Lemma_3_5
