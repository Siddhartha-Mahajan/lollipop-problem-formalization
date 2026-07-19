import Lollipop.Lemma_8_2.Proof

/-!
Manuscript Lemma 8.2 (`lem:chamber`): a realized strict pair code persists on
an open product neighborhood.
-/

namespace Lollipop.Manuscript.Lemma_8_2

open Concrete Concrete.EndToEnd Concrete.EndToEnd.Lower

abbrev Statement (code : StrictPairCode) (L M : Concrete.Lollipop) : Prop :=
  RealizesStrictPairCode code L M ->
    exists U V : Set Concrete.Lollipop,
      IsOpen U /\ IsOpen V /\ L ∈ U /\ M ∈ V /\
      ∀ L' ∈ U, ∀ M' ∈ V, RealizesStrictPairCode code L' M'

end Lollipop.Manuscript.Lemma_8_2
