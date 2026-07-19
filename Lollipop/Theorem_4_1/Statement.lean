import Lollipop.Lemma_5_1.Proof
import Lollipop.Lemma_6_2.Proof

/-!
Manuscript Theorem 4.1 (`thm:colored`): the colored Turan bound for a common
`K_4`-free/`K_5`-free two-graph coloring.

The definitions occurring in the statement are all local to the new
`Lollipop/` tree:

* `ColoredGraph`, `DGraph`, and `EGraph` are defined in the substantive
  colored-Zykov development integrated into `Lollipop/Lemma_5_1/Proof.lean`.
* The four colors have weights `0, 1, 1, 3`.  Consequently
  `orderedColorWeight / 2` is the manuscript quantity
  `|D| + |E| + |D \cap E|`: the ordered sum counts every unordered pair twice.
* `TheoremOneManuscript.manuscriptS` is the sorted four-part maximum appearing
  in the manuscript. Its definition and its equality with the computationally
  useful finite maximum are developed in `Lollipop/Lemma_6_2/Proof.lean`.

This file imports the numbered developments that define its vocabulary, but it
does not import `Theorem_4_1/Proof.lean`. Thus the theorem statement remains a
genuine prerequisite of the final colored-Turan proof, rather than obtaining
its own proof through a reversed import.
-/

namespace Lollipop.Manuscript.Theorem_4_1

universe u

open TheoremOneEndToEnd

abbrev Statement {V : Type u} [Fintype V] [DecidableEq V]
    (C : ColoredGraph V) : Prop :=
  C.DGraph.CliqueFree 4 -> C.EGraph.CliqueFree 5 ->
    C.orderedColorWeight / 2 <=
      TheoremOneManuscript.manuscriptS (Fintype.card V)

end Lollipop.Manuscript.Theorem_4_1
