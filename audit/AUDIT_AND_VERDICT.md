# Audit and verdict

## Manuscript

The manuscript has been rebuilt around arguments that are valid for arbitrary arrangements, including tangencies, coincident circles, overlapping stems, and other degeneracies. After a line-by-line audit, no unresolved mathematical implication or omitted case is known in the final proof.

The most important repairs are:

1. The false rigid-motion lower construction was removed. It is replaced by the polynomial family
   \[
   c_t=(3t,3t),\qquad v_t=(1-t^2,-2t),\qquad r_t=1+t^2,
   \]
   whose distinct members are proved to have exactly `2 + 1 + 0 + 1 = 4` transverse primitive intersections.
2. The unsupported assertion that an extremizer may be assumed generic was removed. The upper bound now uses one-point compactification, Mayer-Vietoris, and Alexander duality to bound the number of complement components for every arrangement.
3. The close-pair, intriguing-pair, and combined pair bounds are proved directly at the level of connected intersection components, so degeneracies cannot increase the count.
4. The five-circle obstruction is proved by uniform radius inflation followed by an explicit four-dimensional bilinear-form argument.
5. The colored extremal step is complete: colored Zykov symmetrization, weighted Turan, the blocker reduction, and the exact `3 x 4` matrix inequality are all proved in the text.
6. The support-compression proof now treats cycles, long paths, double stars, the exceptional `(2,1,1)` degree pattern, `n=0`, and the small cases `1 <= n <= 3` explicitly.
7. The lower base is now all-rational. All six pair tables are decided by strict exact rational inequalities; the smallest absolute decisive value is `151/23400`.
8. Genericization is proved inside an open pairwise chamber by avoiding a finite union of proper real-analytic zero sets.

The exact scripts independently confirm the rational base, the polynomial local family, 646,646 matrix instances through total mass 10, and the colored extremal optimum through 9 vertices. Those checks are corroborative; the all-size proof is symbolic.

**Manuscript verdict:** no known proof hole remains. This is still a new all-`n` result and has not acquired the independent assurance of journal peer review, so the appropriate claim is “fully argued and internally audited,” not “externally certified.”

## Lean

The Lean tree is not an end-to-end formalization of the theorem about actual Euclidean complement regions.

Its public endpoint is

```lean
theorem theorem_one
    (P : TheoremOne.MaxProblemFamily)
    (h : GeometryCertificates P) :
    TheoremOneStatement P
```

Thus the decisive geometry and topology are hypotheses packaged in `GeometryCertificates`. The project itself proves that such a certificate cannot be produced uniformly for an arbitrary abstract `MaxProblemFamily` (`GeometryObstruction.lean`). The source does not instantiate a concrete problem family whose region function is the number of connected components of `R^2` minus a finite union of lollipops.

The bundled static audit strips comments and strings before scanning all Lean sources. It finds no `sorry`, `admit`, top-level `axiom`, `constant`, `opaque`, or `unsafe` declaration. This is useful, but it does not turn a conditional theorem into the desired concrete theorem.

After integration into this repository, `lake build Lollipop` was run
successfully on June 22, 2026.  The build completed all 3320 jobs.

**Lean verdict:** substantial, statically placeholder-free, and kernel-checked
in this repository, but incomplete for the requested certificate-free
Euclidean theorem. The repository labels it accordingly and does not represent
it as a completed formalization.
