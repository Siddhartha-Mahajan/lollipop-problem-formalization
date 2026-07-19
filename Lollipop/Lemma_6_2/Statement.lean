import Lollipop.Lemma_6_2.Proof

/-!
Manuscript Lemma 6.2 (`lem:blocker`): if the two blocker graphs satisfy
`α(A) ≤ 3` and `α(B) ≤ 4`, then

`(3/2) Q + 2 w(A) + 2 w(B) ≥ M(n)`.

For finite simple graphs, the two independence-number conditions are written
as `Aᶜ.CliqueFree 4` and `Bᶜ.CliqueFree 5`.  The proof file constructs both
weighted Turán partitions, their `3 × 4` intersection matrix, and every
intermediate inequality; none of those objects is an assumption.
-/

namespace Lollipop.Manuscript.Lemma_6_2

open Lollipop
open Lollipop.TheoremOneEndToEnd

universe u

abbrev Statement
    {V : Type u} [Fintype V] [DecidableEq V]
    (x : V → Nat) (A B : SimpleGraph V)
    [DecidableRel A.Adj] [DecidableRel B.Adj] : Prop :=
  Aᶜ.CliqueFree 4 →
  Bᶜ.CliqueFree 5 →
    (3 / 2 : Rat) * weightSquareSumRat x +
        2 * weightedEdgeMass x A.Adj +
        2 * weightedEdgeMass x B.Adj ≥
      concreteM (totalWeightNat x)

end Lollipop.Manuscript.Lemma_6_2
