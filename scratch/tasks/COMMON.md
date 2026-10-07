# Common rules for all Lean tasks (read first)

Repository: /Users/siddhartha/Lossfunk/lollipop_end_to_end_formalization (git branch `close-remaining-gaps`).
Lean 4 / Mathlib are pinned by `lean-toolchain` (v4.31.0-rc1). Compile a single file with:

    export PATH=$HOME/.elan/toolchains/leanprover--lean4---v4.31.0-rc1/bin:$PATH
    cd /Users/siddhartha/Lossfunk/lollipop_end_to_end_formalization
    lake env lean scratch/impl/<YourFile>.lean

NEVER run `lake build` (it contends with other workers and rebuilds thousands of modules).
Do NOT modify, move or delete any existing file. Do NOT run git commands that change state
(no commit, checkout, reset, stash). Create only your own file(s) in `scratch/impl/`.

The shared specification is `scratch/Spec.lean` (read it; it compiles with `sorry`s). Your job is
to PROVE the theorem(s) assigned to you, with exactly the statement given there, in a new file
`scratch/impl/<Name>.lean`. Because scratch files cannot be imported, copy the definitions you need
(`Pieces.perp`, `circlePt`, `stemPt`, `circleArcSet`, ..., `Collars`, `OneCollar`, `Germ`,
`IsSphereArc`) verbatim from Spec.lean into your file, inside the same namespace
`Lollipop.Concrete.EndToEnd.Pieces`, then prove the theorem. Helper lemmas are welcome (keep them in
your file). You may `import` any existing module of the form `old_lean_folder.Concrete.EndToEnd.*`,
`old_lean_folder.JordanCurveTheorem.*` and Mathlib. The same set of imports used at the top of Spec.lean
is a good starting point. (Existing archived modules give you: `Lollipop` structure with `center`, `radial`,
`radius = ‖radial‖`, `anchor`, `circle`, `stem`, `stemMap t = center + t • radial`, the Jordan curve theorem
`JordanCurveTheorem.jordan_curve_theorem`, `IsSimpleArcEnd`, `IsSimpleClosedCurve`, `isSimpleArcEnd_trans`,
`SimpleArcComplement.isConnected_compl`, `ArcClosedCurve.isSimpleClosedCurve_union_of_two_arcs`,
`Sphere2 = OnePoint Point`, `finitePoint`, `infinity`, `finiteLift`, `hatCarrier`, ...; grep them.)

Hard requirements:
  * No `sorry`, no `admit`, no new `axiom`, no `native_decide`. At the end of your file add
    `#print axioms <each final theorem>`; the output must list only `propext`, `Classical.choice`, `Quot.sound`.
  * The final theorem statements must be identical to Spec.lean (same hypotheses, same conclusion).
    If you believe a statement is FALSE or needs an extra hypothesis, STOP and report exactly why with a
    concrete counterexample or the minimal missing hypothesis; do not silently change it.
  * Prefer robust proofs (explicit terms, `nlinarith`/`linarith`/`field_simp`/`positivity`), avoid fragile `simp` chains.
    Compile often; fix errors incrementally. Mathlib names change: grep `.lake/packages/mathlib/Mathlib` to confirm.

When finished, reply with: (1) the file path, (2) the `#print axioms` output, (3) a 5-line summary of the proof
architecture, (4) anything the integrator must know (extra lemmas, deviations).
