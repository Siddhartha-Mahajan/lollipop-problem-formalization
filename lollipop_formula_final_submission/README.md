# A Colored Turán Proof of the Exact Lollipop Formula

This is the final manuscript and reproducibility bundle. It contains a single,
self-contained LaTeX source file, the compiled PDF, and ancillary verification
programs. No Lean files are included.

## Main result

For every integer `n >= 0`, with

```text
R = {1, 2, 8, 14, 15},
chi(n) = 1 when n mod 16 is in R, and 0 otherwise,
```

the paper proves

```text
S(n) = floor(33 n^2 / 32) - chi(n),
a_L(n) = floor(97 n^2 / 32) - n + 1 - chi(n).
```

The upper bound applies to arbitrary arrangements, including degenerate ones.
The lower bound is realized by a generic four-cluster construction.

## Bundle layout

- `manuscript/lollipop_formula.tex` — complete LaTeX source.
- `manuscript/lollipop_formula.pdf` — compiled manuscript.
- `scripts/certify_rational_base.py` — exact rational verification of the
  four-lollipop base; regenerates the JSON, text, and CSV certificate.
- `scripts/verify_local_family.py` — exact symbolic checks and supplementary
  rational/numerical checks for the polynomial local family.
- `scripts/verify_closed_form.py` — integer-only verification of the period-16
  formulas and displayed optimal quadruples for `0 <= n <= 4096`.
- `scripts/run_all_checks.py` — runs all three checks and compares all 66
  appendix entries with the regenerated CSV certificate.
- `verification/` — machine-readable and human-readable checker outputs.
- `CHANGELOG.md` — substantive revisions made to the manuscript.
- `SHA256SUMS` — checksums for all distributed files.

## Compile the manuscript

A standard current TeX Live installation is sufficient. From the bundle root:

```bash
cd manuscript
latexmk -pdf -interaction=nonstopmode -halt-on-error lollipop_formula.tex
```

The manuscript has no external figures, bibliography database, or custom style
files.

## Run the ancillary checks

Python 3.10 or later is recommended. Install the sole non-standard dependency:

```bash
python3 -m pip install -r requirements.txt
```

Then run:

```bash
python3 scripts/run_all_checks.py
```

A successful run ends with:

```text
Appendix-to-CSV comparison: 66 exact rows matched.
ALL CHECKS PASSED
```

The rational-base decisions use `fractions.Fraction`; decimal values are output
only for readability. The computational checks are reproducibility aids. The
proofs of the geometric, combinatorial, and arithmetic statements are included
in the manuscript and do not depend on a finite computer search.
