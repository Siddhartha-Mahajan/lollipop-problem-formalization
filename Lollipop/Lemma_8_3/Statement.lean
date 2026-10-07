import Lollipop.Lemma_8_3.Proof

/-!
Manuscript Lemma 8.3 (`lem:local4`): the polynomial family starts at the
standard unit lollipop and every two ordered members in `[0, 1/4]` have four
transverse crossings, none at an anchor.
-/

namespace Lollipop.Manuscript.Lemma_8_3

open Concrete Concrete.EndToEnd Concrete.EndToEnd.Lower

def Statement : Prop :=
  Continuous PolynomialFamily.member /\
  PolynomialFamily.member 0 = standardLollipop /\
  (forall {s t : Real}, 0 <= s -> s < t -> t <= (1 : Real) / 4 ->
    pairCrossingCount (PolynomialFamily.member s) (PolynomialFamily.member t) = 4 /\
    PrimitivePairwiseTransverse
      (PolynomialFamily.member s) (PolynomialFamily.member t) /\
    (PolynomialFamily.member s).anchor ∉
      pairCrossingSet (PolynomialFamily.member s) (PolynomialFamily.member t) /\
    (PolynomialFamily.member t).anchor ∉
      pairCrossingSet (PolynomialFamily.member s) (PolynomialFamily.member t))

end Lollipop.Manuscript.Lemma_8_3
