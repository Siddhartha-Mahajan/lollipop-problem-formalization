import Lollipop.Lemma_3_2.Proof

/-!
Manuscript Lemma 3.2 (`lem:intr-mixed`): for an intersecting intriguing pair,
each outside mixed component has at most one point, and two such components
force the finite ray--ray intersection to be empty.
-/

namespace Lollipop.Manuscript.Lemma_3_2

open Concrete Concrete.EndToEnd

def Statement : Prop :=
  forall (L M : Concrete.Lollipop),
    PairGeometry.normSqPoint (M.center - L.center) <=
      L.radius ^ 2 + M.radius ^ 2 ->
    (rc L M \ cc L M).ncard <= 1 /\
    (cr L M \ cc L M).ncard <= 1 /\
    (((rc L M \ cc L M).Nonempty /\ (cr L M \ cc L M).Nonempty) ->
      rr L M = ∅)

end Lollipop.Manuscript.Lemma_3_2
