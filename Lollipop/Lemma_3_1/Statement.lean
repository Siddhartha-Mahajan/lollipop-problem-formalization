import Lollipop.Lemma_3_1.Proof

/-!
Manuscript Lemma 3.1 (`lem:close-mixed`): a close pair has at most two mixed
ray--circle intersection points in total.
-/

namespace Lollipop.Manuscript.Lemma_3_1

open Concrete Concrete.EndToEnd

def Statement : Prop :=
  forall (L M : Concrete.Lollipop), PairGeometry.Close L M ->
    (cr L M).ncard + (rc L M).ncard <= 2

end Lollipop.Manuscript.Lemma_3_1
