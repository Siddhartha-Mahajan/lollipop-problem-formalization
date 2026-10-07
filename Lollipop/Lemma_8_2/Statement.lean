import Lollipop.Lemma_8_2.Proof

/-!
Manuscript Lemma 8.2 (`lem:chamber`): for every pair whose circles are neither
tangent nor coincident (crossing, apart, or nested), whose accepted mixed
intersections are transverse and away from anchors, and whose stems are
nonparallel with line intersection away from the anchors, all strict conditions
persist and each of the four component counts is constant on an open product
neighborhood.
-/

namespace Lollipop.Manuscript.Lemma_8_2

open Concrete Concrete.EndToEnd Concrete.EndToEnd.Lower

abbrev Statement (code : GeneralStrictPairCode) (L M : Concrete.Lollipop) : Prop :=
  GeneralRealizesStrictPairCode code L M ->
    exists U V : Set Concrete.Lollipop,
      IsOpen U /\ IsOpen V /\ L ∈ U /\ M ∈ V /\
      ∀ L' ∈ U, ∀ M' ∈ V, GeneralRealizesStrictPairCode code L' M' /\
        (cc L' M').ncard = (cc L M).ncard /\
        (rc L' M').ncard = (rc L M).ncard /\
        (cr L' M').ncard = (cr L M).ncard /\
        (rr L' M').ncard = (rr L M).ncard

end Lollipop.Manuscript.Lemma_8_2
