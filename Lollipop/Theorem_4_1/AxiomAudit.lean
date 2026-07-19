import Lollipop.Theorem_4_1.Proof

/-!
Kernel dependency audit for the manuscript-numbered Theorem 4.1.

The first line audits the public numbered theorem. The remaining lines expose
the same information for the major numbered and implementation layers, making
it easier to notice if a later edit introduces a new assumption below the
top-level proof.
-/

universe u

-- Check explicitly that the theorem in `Proof.lean` proves the public
-- proposition declared in `Statement.lean` (not merely a private surrogate).
example {V : Type u} [Fintype V] [DecidableEq V]
    (C : Lollipop.TheoremOneEndToEnd.ColoredGraph V) :
    Lollipop.Manuscript.Theorem_4_1.Statement C :=
  Lollipop.Manuscript.Theorem_4_1.proof C

#print axioms Lollipop.Manuscript.Theorem_4_1.proof
#print axioms Lollipop.Manuscript.Lemma_5_1.proof
#print axioms Lollipop.TheoremOneEndToEnd.zeroTwin_colored_turan_bound
#print axioms Lollipop.TheoremOneEndToEnd.colored_turan_bound
#print axioms Lollipop.TheoremOneEndToEnd.exists_partition_bound_of_cliqueFree
#print axioms Lollipop.matrix_theorem_proven
#print axioms Lollipop.TheoremOneManuscript.manuscriptS_eq_concreteS
