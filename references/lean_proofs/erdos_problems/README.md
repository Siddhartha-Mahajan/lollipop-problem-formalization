# External Erdős Lean Proof References

These files are downloaded reference material, not part of the lollipop
build.  They are here to study how other Erdős-problem formalizations organize
full Lean proofs.

Source repository:

- `plby/lean-proofs`
- path: `src/v4.24.0/ErdosProblems/`
- repository README saved as `../README.plby.md`
- directory listing saved as `github_contents_plby_ErdosProblems.json`

The proof files themselves record:

- Lean toolchain: `leanprover/lean4:v4.24.0`
- Mathlib commit: `f897ebcf72cd16f89ab4577d0c826cd14afaafc7`

This lollipop repository currently uses Lean `v4.31.0-rc1`, so these files
are not expected to build directly in this Lake project.  A direct test of
`Erdos794.lean` failed here because this project does not have the aggregate
`Mathlib.olean` built.  `Erdos618.lean` also imports `ErdosProblems.Erdos134`,
so it requires the source repository's module layout.

## Downloaded Full Proof Files

The selected sample emphasizes graph, Ramsey, chromatic, and Turán-adjacent
examples:

- `Erdos134.lean`: graph theory, Alon-style probabilistic construction.
- `Erdos582.lean`: graph Ramsey/Folkman construction.
- `Erdos618.lean`: graph theorem depending on `Erdos134.lean`.
- `Erdos666.lean`: graph theory disproof.
- `Erdos762.lean`: chromatic-number disproof.
- `Erdos794.lean`, `Erdos794b.lean`, `Erdos794c.lean`: hypergraph/Turán
  disproof variants.
- `Erdos1007.lean`, `Erdos1008.lean`: finite graph/extremal examples.
- `Erdos1028.lean`: graph discrepancy/probabilistic proof.
- `Erdos1034.lean`, `Erdos1036.lean`, `Erdos1037.lean`: graph-theoretic
  solved/disproved examples.
- `Erdos1067.lean`: infinite graph/set-theoretic disproof.
- `Erdos1080.lean`: finite-field graph construction.

Text scan result on the downloaded proof sample:

- no `sorry`;
- no `admit`;
- no top-level `axiom`, `constant`, `opaque`, or `unsafe`;
- many files include a final `#print axioms` command and comment.

Most printed axiom comments are exactly:

```text
[propext, Classical.choice, Quot.sound]
```

Two finite-computation/reduction-style variants in this sample mention
`Lean.ofReduceBool` and `Lean.trustCompiler`.  That is a warning sign for the
lollipop project: the final lollipop theorem should avoid trusted-computation
dependencies in the theorem spine.

## Statement-Only Contrast

The file

```text
../../formal_conjectures/erdos_similar/1067.lean
```

is from `google-deepmind/formal-conjectures`.  It is intentionally
statement-only and contains `sorry`, but it includes the `formal_proof` link to
the full proof source in `plby/lean-proofs`.  This is useful as provenance, but
it is not a proof source.

## Lessons For The Lollipop Repo

- Keep a single final theorem endpoint and make it easy to find.
- Put the exact source/provenance note near the theorem file.
- Record the Lean toolchain and Mathlib commit used by any external reference.
- Include `#print axioms` output for the public endpoint.
- Prefer ordinary theorem dependencies over certificate bundles that restate
  the main work as assumptions.
- Avoid final reliance on `native_decide`, `Lean.trustCompiler`, or opaque
  external computation if the claim is meant to satisfy the strictest Lean
  verification standard.
