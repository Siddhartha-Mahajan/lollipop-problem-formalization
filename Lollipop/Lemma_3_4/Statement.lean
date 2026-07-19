import Lollipop.Lemma_3_4.Proof

/-!
Manuscript Lemma 3.4 (`lem:forced-close`): every four stem directions contain
a close pair.
-/

namespace Lollipop.Manuscript.Lemma_3_4

open Concrete Concrete.EndToEnd

def Statement : Prop :=
  forall {n : Nat} (A : Arrangement n) (t : Finset (Fin n)), t.card = 4 ->
    ∃ i ∈ t, ∃ j ∈ t,
      i ≠ j /\ PairGeometry.Close (A i) (A j)

end Lollipop.Manuscript.Lemma_3_4
