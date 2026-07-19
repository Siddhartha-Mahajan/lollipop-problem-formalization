import Lollipop.Proposition_3_3.Proof

/-!
Manuscript Proposition 3.3 (`prop:pair-savings`): the universal, close,
intriguing, and combined close/intriguing pair-excess bounds.
-/

namespace Lollipop.Manuscript.Proposition_3_3

open Concrete Concrete.EndToEnd

def Statement : Prop :=
  forall (L M : Concrete.Lollipop),
    pairExcess L M <= 7 /\
    (PairGeometry.Close L M -> pairExcess L M <= 5) /\
    (PairGeometry.Intriguing L M -> pairExcess L M <= 5) /\
    (PairGeometry.Close L M -> PairGeometry.Intriguing L M ->
      pairExcess L M <= 4)

end Lollipop.Manuscript.Proposition_3_3
