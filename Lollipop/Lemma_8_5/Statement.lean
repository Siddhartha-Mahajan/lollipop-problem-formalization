import Lollipop.Lemma_8_5.Proof

/-!
Manuscript Lemma 8.5 (`lem:blowup`): every admissible four-cluster size vector
has a generic realization with the Karlsson lower crossing polynomial.
-/

namespace Lollipop.Manuscript.Lemma_8_5

open Concrete Concrete.EndToEnd Concrete.EndToEnd.Lower

abbrev Statement {n : Nat} (q : QuadVec n) : Prop :=
  GenericityPort.ChamberGenericityAvoidance n ->
  q ∈ quadVecs n ->
    exists A : Arrangement n,
      IsGeneric A /\
      ((totalCrossingsNat A : Nat) : Rat) = lowerCrossingsOfQuad q

end Lollipop.Manuscript.Lemma_8_5
