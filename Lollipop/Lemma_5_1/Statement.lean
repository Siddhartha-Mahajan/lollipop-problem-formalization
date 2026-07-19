import Lollipop.Lemma_5_1.Proof

/-!
Manuscript Lemma 5.1 (`lem:zykov`): a feasible coloring can be replaced by an
objective-maximal zero-twin quotient-ready coloring, i.e. a blow-up with
constant nonzero colors between zero-twin classes.
-/

namespace Lollipop.Manuscript.Lemma_5_1

universe u

open TheoremOneEndToEnd

abbrev Statement {V : Type u} [Fintype V] [DecidableEq V]
    (C : ColoredGraph V) : Prop :=
  C.DGraph.CliqueFree 4 /\ C.EGraph.CliqueFree 5 ->
    exists Cmax : ColoredGraph V,
      Cmax.IsColoredZykovExtremal /\
      C.orderedColorWeight <= Cmax.orderedColorWeight /\
      Cmax.ZeroTwinQuotientReady

end Lollipop.Manuscript.Lemma_5_1
