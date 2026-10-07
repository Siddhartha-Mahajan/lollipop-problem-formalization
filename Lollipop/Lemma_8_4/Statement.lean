import Lollipop.Lemma_8_4.Proof

/-!
Manuscript Lemma 8.4 (`lem:genericize`): every nonempty strict pair chamber
contains a generic arrangement with the same pairwise component counts.
-/

namespace Lollipop.Manuscript.Lemma_8_4

open Concrete Concrete.EndToEnd Concrete.EndToEnd.Lower

abbrev Statement {n : Nat} (S : PairCodeSpec n) (A : Arrangement n) : Prop :=
  RealizesPairCodeSpec S A ->
    exists B : Arrangement n,
      IsGeneric B /\
      forall i j : Fin n, i < j ->
        pairCrossingCount (B i) (B j) = (S.code i j).crossings

end Lollipop.Manuscript.Lemma_8_4
