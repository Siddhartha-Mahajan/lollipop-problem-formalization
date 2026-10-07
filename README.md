# Lollipop formula formalization

This repository contains the lollipop-formula manuscripts and a Lean
development organized by the theorem numbering in the main manuscript.

## Start here

- Main manuscript source: `manuscript/main_manuscript/main.tex`
- Main manuscript PDF: `manuscript/main_manuscript/main.pdf`
- More detailed treatment of `S(n)`: `manuscript/more_detailed_S_n.tex`
- Rendered detailed manuscript: `manuscript/more_detailed_S_n.pdf`
- Manuscript-numbered Lean map and verification verdict: `Lollipop/README.md`
- Lean root module: `Lollipop.lean`
- Archived pre-reorganization Lean tree: `old_lean_folder/`

## Manuscripts

Rebuild the main paper with:

```sh
cd manuscript/main_manuscript
tectonic main.tex
```

Rebuild the detailed `S(n)` paper with:

```sh
cd manuscript
tectonic more_detailed_S_n.tex
```

The detailed source is a byte-for-byte copy of
`lollipop_formula_final_submission/manuscript/lollipop_formula.tex`, placed in
the main manuscript area under a descriptive name.

## Lean layout

The new `Lollipop/` tree mirrors every numbered theorem-like result in
`main.tex`. For example:

```text
Lollipop/
├── Theorem_1_1/
│   ├── Statement.lean
│   └── Proof.lean
├── Proposition_2_1/
│   ├── Statement.lean
│   └── Proof.lean
├── Lemma_3_1/
│   ├── Statement.lean
│   └── Proof.lean
└── …
```

There are 19 numbered result directories, each with a separate statement and
proof file. `Lollipop/README.md` gives the complete mapping from LaTeX labels
to Lean paths and local proof endpoints.

The implementation required by those numbered results is integrated directly
into the numbered `Proof.lean` files. Consequently the new `Lollipop/` source
tree has neither a generic implementation subtree nor a concrete-geometry
subtree, and it has no dependency on `old_lean_folder/`. Its project imports
resolve only to other numbered files, with Mathlib providing the standard
library dependencies.

The pre-reorganization source remains separately preserved in
`old_lean_folder/` for comparison, but it is not imported by the new tree.

Build the numbered formalization with:

```sh
lake build Lollipop
```

The target was verified successfully on October 8, 2026 across 3,530 build
jobs.

The full “Did you prove it?” audit is recorded in `Lollipop/README.md`.
All 19 numbered proof terms compile and use only
`[propext, Classical.choice, Quot.sound]`, and (as of October 8, 2026) all 19
prove their full corresponding manuscript statements, including the previously
conditional Theorem 1.1 and Proposition 2.1 (see the caveat on `S(n)` in
`Lollipop/README.md`).  The axiom results can be reproduced with:

```sh
lake env lean Lollipop/NumberedAxiomAudit.lean
```

## Formalization boundary

The numbered tree has no remaining hypotheses packages:

- Theorem 1.1 is proved for concrete Euclidean lollipops
  (`Theorem_1_1/Concrete.lean`); the abstract-family assembly is kept only as
  `proof_of_package`.
- Proposition 2.1 is proved unconditionally
  (`Proposition_2_1/Unconditional.lean`); the planar-topology package is proved
  in `Lollipop/Topology/` using the Jordan curve library in
  `JordanCurveTheorem/` and the carrier-cutting theorem.

`old_lean_folder/` is an archive and not a build dependency of `Lollipop`; it
still contains the old unfinished topology assembly with one `sorry`
(`effectiveLocalizedCarrierSubdivisionData_exists`), now superseded by the
proof in `Lollipop/Topology/Carrier/`.

No Lean file in the transitive build closure of `Lollipop` contains `sorry`,
`admit`, or a project axiom.

## Repository layout

```text
Lollipop.lean
Lollipop/                  # numbered façade, implementation, and Topology/ (carrier cutting)
JordanCurveTheorem/        # Jordan curve theorem library
old_lean_folder/           # archived substantive development
manuscript/
  main_manuscript/
  more_detailed_S_n.tex
  more_detailed_S_n.pdf
lollipop_formula_final_submission/
references/
lakefile.lean
lake-manifest.json
lean-toolchain
```
