# Theorem 4.1: proof guide

The manuscript states that if `D` and `E` are graphs on the same `n` vertices,
`D` is `K₄`-free, and `E` is `K₅`-free, then

```text
|D| + |E| + |D ∩ E| ≤ S(n).
```

The Lean statement represents the two graphs by one four-coloring:

| color | membership | weight |
|---|---|---:|
| `zero` | neither graph | 0 |
| `A` | `E \ D` | 1 |
| `B` | `D \ E` | 1 |
| `X` | `D ∩ E` | 3 |

`DGraph` selects colors `B` and `X`; `EGraph` selects colors `A` and `X`.
Thus the color weight of an unordered pair is exactly its contribution to
`|D| + |E| + |D ∩ E|`.  Lean's `orderedColorWeight` counts both orientations,
so the theorem divides it by two.

## Where the names in `Proof.lean` come from

1. `ColoredGraph`, `DGraph`, `EGraph`, `orderedColorWeight`, and the complete
   colored-Zykov cloning proof are in `Lollipop/Lemma_5_1/Proof.lean`.
2. `Lollipop.Manuscript.Lemma_5_1.proof` is the numbered façade for the Zykov
   reduction.  It returns an extremal feasible coloring `Cmax`, proves that the
   original objective is no larger, and proves that `Cmax` is ready for the
   zero-twin quotient.
3. `zeroTwin_colored_turan_bound` is proved earlier in
   `Lollipop/Theorem_4_1/Proof.lean`. It forms the quotient, proves preservation
   of the objective, and passes the concrete quotient data to the lower layers.
4. The weighted Turan theorem that produces the `3`- and `4`-partitions is
   proved in `Lollipop/Lemma_6_1/Proof.lean`.
5. Intersection of those partitions into the `3 × 4` matrix and the blocker
   algebra are proved in `Lollipop/Lemma_6_2/Proof.lean`.
6. Support descent and the star-forest cases are proved in
   `Lollipop/Lemma_7_2/Proof.lean` and `Lollipop/Lemma_7_3/Proof.lean`; their
   final matrix-theorem assembly is in `Lollipop/Theorem_7_1/Proof.lean`.
7. `manuscriptS_eq_concreteS` is proved in
   `Lollipop/Lemma_6_2/Proof.lean`; it identifies the finite maximum used
   internally with the sorted four-part definition printed in the manuscript.

## What “certificate” means in internal filenames

Some inherited internal identifiers contain the word `Certificate`.  These
are dependent Lean records: they bundle a quotient, weights, partitions, or a
matrix together with proofs of the required properties.  Theorem 4.1 does not
take any such record as an assumption.  Its proof constructs every record from
`C`, the `K₄`-free proof, and the `K₅`-free proof.

There are no external certificate files, unchecked solver outputs,
`native_decide`, `sorry`, `admit`, or project axioms in Theorem 4.1's transitive
Lean dependency closure.  `AxiomAudit.lean` asks Lean to print the kernel axiom
dependencies of both the numbered theorem and the underlying library endpoint.
