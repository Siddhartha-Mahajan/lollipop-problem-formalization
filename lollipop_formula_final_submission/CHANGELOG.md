# Revision summary

This version substantially revises the supplied manuscript into a
self-contained submission bundle.

## Mathematical revisions

- Replaced the optimization-only statement of the answer by the exact closed
  forms
  
  `S(n) = floor(33 n^2 / 32) - 1_{n mod 16 in {1,2,8,14,15}}`
  
  and
  
  `a_L(n) = floor(97 n^2 / 32) - n + 1 - 1_{n mod 16 in {1,2,8,14,15}}`.
- Reduced the four-variable minimization defining `M(n)` to a one-variable
  parity-sensitive quadratic, evaluated it residue by residue modulo 16, and
  recorded a periodic optimal quadruple for every residue.
- Strengthened Theorem 4.1 to an explicit sharp `n`-only colored Turán bound.
- Added the elementary four-part graph construction proving sharpness of the
  colored extremal theorem independently of the geometry.
- Clarified the universal-coefficient step in the topological argument.
- Made the zero-twin and weighted-twin tie-breaker arguments explicit by
  noting that no other twin class splits under cloning.
- Added an explicit termination argument for support compression.
- Streamlined the small-`n` part of the star-forest estimate using the exact
  formula for `M(n)`.
- Clarified the non-coincidence argument in the local four-crossing family.

## Certificate and reproducibility revisions

- Moved the complete exact rational certificate into an appendix of the paper.
  The appendix contains all 66 decisive signs and reduced fractions.
- Added an exact appendix-to-CSV comparison to the one-command verification
  runner.
- Added an independent integer-only checker for the period-16 formula and
  optimizer pattern.
- Retained the exact rational base verifier and symbolic local-family checker,
  with clearly named outputs.
- Added a README, dependency file, manifest, and SHA-256 checksums.

## Editorial revisions

- Reorganized the opening section around the exact theorem and a four-layer
  proof outline.
- Improved theorem names, cross-references, notation, and transitions.
- Removed development-history language and externalized proof obligations.
- Updated and normalized the bibliography metadata.
- Reworked the appendix table for legible exact fractions.
- Excluded all Lean, audit, and intermediate build files from the final bundle.
