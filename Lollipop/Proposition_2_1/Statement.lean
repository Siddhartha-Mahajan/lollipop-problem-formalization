import Lollipop.Proposition_2_1.Proof

/-!
Manuscript Proposition 2.1 (`prop:top-region`): the arbitrary-arrangement
topological region inequality, together with its generic equality clause.
-/

namespace Lollipop.Manuscript.Proposition_2_1

open Concrete Concrete.EndToEnd

def Statement : Prop :=
  (forall {n : Nat} (A : Arrangement n),
      regionCountRat A - (n : Rat) - 1 <= pairSum n (pairExcessTable A)) /\
  (forall {n : Nat} {A : Arrangement n}, IsGeneric A ->
      regionCountRat A = ((totalCrossingsNat A : Nat) : Rat) + (n : Rat) + 1)

end Lollipop.Manuscript.Proposition_2_1
