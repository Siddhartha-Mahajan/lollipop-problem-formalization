# Archived Lean development

This is the former `Lollipop/` directory, preserved when the project was
reorganized around the theorem numbers in the manuscript.

The only mechanical change made during the move was rewriting module imports
from `Lollipop.…` to `old_lean_folder.…`, which is required because Lean module
names follow filesystem paths. Declarations and proof bodies retain their
original `Lollipop` namespaces so the new manuscript-numbered façade can cite
them directly.

The previously deleted `JordanCurveTheorem/`, `audit/`, and `expected_fail/`
trees have also been restored from Git and copied here. The archived Jordan
modules and their lollipop consumers import
`old_lean_folder.JordanCurveTheorem.…`, keeping this archive self-contained.
