import Lollipop

/-!
Kernel-axiom audit for every manuscript-numbered proof endpoint.

Run from the repository root with:

```sh
lake env lean Lollipop/NumberedAxiomAudit.lean
```

Every reported list must be a subset of
`[propext, Classical.choice, Quot.sound]`.  This audit answers only the axiom
question.  It does not by itself establish that a Lean statement is an exact
translation of the corresponding manuscript statement; that semantic audit is
recorded in `Lollipop/README.md`.
-/

#print axioms Lollipop.Manuscript.Theorem_1_1.proof
#print axioms Lollipop.Manuscript.Proposition_2_1.proof
#print axioms Lollipop.Manuscript.Lemma_3_1.proof
#print axioms Lollipop.Manuscript.Lemma_3_2.proof
#print axioms Lollipop.Manuscript.Proposition_3_3.proof
#print axioms Lollipop.Manuscript.Lemma_3_4.proof
#print axioms Lollipop.Manuscript.Lemma_3_5.proof
#print axioms Lollipop.Manuscript.Theorem_4_1.proof
#print axioms Lollipop.Manuscript.Lemma_5_1.proof
#print axioms Lollipop.Manuscript.Lemma_6_1.proof
#print axioms Lollipop.Manuscript.Lemma_6_2.proof
#print axioms Lollipop.Manuscript.Theorem_7_1.proof
#print axioms Lollipop.Manuscript.Lemma_7_2.proof
#print axioms Lollipop.Manuscript.Lemma_7_3.proof
#print axioms Lollipop.Manuscript.Proposition_8_1.proof
#print axioms Lollipop.Manuscript.Lemma_8_2.proof
#print axioms Lollipop.Manuscript.Lemma_8_3.proof
#print axioms Lollipop.Manuscript.Lemma_8_4.proof
#print axioms Lollipop.Manuscript.Lemma_8_5.proof
