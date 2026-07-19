import Lollipop.Lemma_6_1.Proof

/-!
Manuscript Lemma 6.1 (`lem:weighted-turan`), in the equivalent ordered-edge
partition form used by the formalization.
-/

namespace Lollipop.Manuscript.Lemma_6_1

universe u

open TheoremOneEndToEnd

abbrev Statement {V : Type u} [Fintype V] [DecidableEq V]
    (x : V -> Nat) (G : SimpleGraph V) [DecidableRel G.Adj]
    (r : Nat) : Prop :=
  0 < r -> G.CliqueFree (r + 1) ->
    exists p : V -> Fin r,
      orderedRelWeight x G.Adj <=
        (totalWeightNat x : Rat) ^ 2 - partitionSquareWeight x p

end Lollipop.Manuscript.Lemma_6_1
