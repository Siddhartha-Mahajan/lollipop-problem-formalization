# Audit Material

This folder keeps the audit notes, verification outputs, and verification
scripts separate from the manuscript and Lean source.

Important files:

- `AUDIT_AND_VERDICT.md`: mathematical and Lean verdict.
- `FORMALIZATION_STATUS.md`: exact Lean boundary.
- `proof_audit_checklist.md`: layer-by-layer proof checklist.
- `theorem_dependency_map.md`: high-level theorem dependency map.
- `verification/`: saved script outputs.
- `scripts/`: reproducible verification scripts.

Run scripts from the repository root, for example:

```sh
python3 audit/scripts/audit_lean.py
```
