import Lollipop.Proposition_8_1.Proof

/-!
Manuscript Proposition 8.1 (`prop:base`): the exact rational four-lollipop
base realizes the six strict component codes `5, 7, 7, 7, 7, 7`, hence has
forty pairwise crossings.
-/

namespace Lollipop.Manuscript.Proposition_8_1

open Concrete Concrete.EndToEnd Concrete.EndToEnd.Lower

def Statement : Prop :=
  RealizesStrictPairCode StrictPairCode.five RationalBase.Q0 RationalBase.Q1 /\
  RealizesStrictPairCode StrictPairCode.seven RationalBase.Q0 RationalBase.Q2 /\
  RealizesStrictPairCode StrictPairCode.seven RationalBase.Q0 RationalBase.Q3 /\
  RealizesStrictPairCode StrictPairCode.seven RationalBase.Q1 RationalBase.Q2 /\
  RealizesStrictPairCode StrictPairCode.seven RationalBase.Q1 RationalBase.Q3 /\
  RealizesStrictPairCode StrictPairCode.seven RationalBase.Q2 RationalBase.Q3 /\
  pairCrossingCount RationalBase.Q0 RationalBase.Q1 +
    pairCrossingCount RationalBase.Q0 RationalBase.Q2 +
    pairCrossingCount RationalBase.Q0 RationalBase.Q3 +
    pairCrossingCount RationalBase.Q1 RationalBase.Q2 +
    pairCrossingCount RationalBase.Q1 RationalBase.Q3 +
    pairCrossingCount RationalBase.Q2 RationalBase.Q3 = 40

end Lollipop.Manuscript.Proposition_8_1
