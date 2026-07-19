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

The reorganized target was verified successfully on July 19, 2026 across
3,276 build jobs.

The full “Did you prove it?” audit is recorded in `Lollipop/README.md`.
All 19 numbered proof terms compile and use only
`[propext, Classical.choice, Quot.sound]`, but only 13 currently prove their
full corresponding manuscript statements.  The remaining six are
conditional or narrower formulations; the README identifies the exact gap in
each case.  The axiom results can be reproduced with:

```sh
lake env lean Lollipop/NumberedAxiomAudit.lean
```

## Formalization boundary

The numbered façade preserves the proof boundary of the substantive work:

- Theorem 1.1 is a checked assembly from explicitly named upper-geometry and
  Karlsson lower-construction subtheorems.
- Proposition 2.1 takes the concrete `PlanarTopologyPorts` package explicitly.
- Lemmas 8.4 and 8.5 take the chamber-avoidance proof package explicitly.
- The remaining numbered wrappers invoke proved endpoints contained in the
  same `Lollipop/` tree.

The former `JordanCurveTheorem/`, `audit/`, and `expected_fail/` trees are
preserved only under `old_lean_folder/`; they are not part of the live source
tree. Proposition 2.1 deliberately remains at the clean `PlanarTopologyPorts`
interface instead of importing the later, separate topology assembly that
contains a pre-existing unfinished proof.

No Lean file in the new self-contained transitive build closure contains
`sorry`, `admit`, or a project axiom.

## Repository layout

```text
Lollipop.lean
Lollipop/                  # self-contained numbered façade and implementation
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
