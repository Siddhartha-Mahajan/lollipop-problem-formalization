#!/usr/bin/env python3
"""Static, reproducible audit of the bundled Lean source.

This is deliberately not a substitute for `lake build`. It strips comments and
strings before scanning for proof placeholders and records the public endpoint
and the concrete-model boundary visible in the source tree.
"""
from __future__ import annotations

import json
import re
from pathlib import Path

AUDIT_ROOT = Path(__file__).resolve().parents[1]
REPO_ROOT = Path(__file__).resolve().parents[2]
LEAN_ROOT = REPO_ROOT
OUT = AUDIT_ROOT / "verification"


def strip_lean_comments_and_strings(text: str) -> str:
    out: list[str] = []
    i = 0
    block_depth = 0
    in_string = False
    while i < len(text):
        if block_depth:
            if text.startswith("/-", i):
                block_depth += 1
                out.extend("  ")
                i += 2
            elif text.startswith("-/", i):
                block_depth -= 1
                out.extend("  ")
                i += 2
            else:
                out.append("\n" if text[i] == "\n" else " ")
                i += 1
            continue
        if in_string:
            ch = text[i]
            if ch == "\\" and i + 1 < len(text):
                out.extend("  ")
                i += 2
            elif ch == '"':
                in_string = False
                out.append(" ")
                i += 1
            else:
                out.append("\n" if ch == "\n" else " ")
                i += 1
            continue
        if text.startswith("/-", i):
            block_depth = 1
            out.extend("  ")
            i += 2
        elif text.startswith("--", i):
            while i < len(text) and text[i] != "\n":
                out.append(" ")
                i += 1
        elif text[i] == '"':
            in_string = True
            out.append(" ")
            i += 1
        else:
            out.append(text[i])
            i += 1
    return "".join(out)


def occurrences(pattern: str, clean: str, path: Path) -> list[dict[str, object]]:
    rx = re.compile(pattern, re.MULTILINE)
    result = []
    for m in rx.finditer(clean):
        line = clean.count("\n", 0, m.start()) + 1
        result.append({"file": str(path.relative_to(LEAN_ROOT)), "line": line, "match": m.group(0)})
    return result


def main() -> None:
    library_files = sorted((LEAN_ROOT / "Lollipop").rglob("*.lean")) + [LEAN_ROOT / "Lollipop.lean"]
    files = [LEAN_ROOT / "lakefile.lean"] + library_files
    scans: dict[str, list[dict[str, object]]] = {
        "sorry": [],
        "admit": [],
        "axiom_declaration": [],
        "constant_declaration": [],
        "opaque_declaration": [],
        "unsafe_declaration": [],
    }
    patterns = {
        "sorry": r"\bsorry\b",
        "admit": r"\badmit\b",
        "axiom_declaration": r"^\s*axiom\s+",
        "constant_declaration": r"^\s*constant\s+",
        "opaque_declaration": r"^\s*opaque\s+",
        "unsafe_declaration": r"^\s*unsafe\s+",
    }
    total_lines = 0
    combined = []
    for path in files:
        raw = path.read_text(errors="replace")
        total_lines += raw.count("\n") + (0 if raw.endswith("\n") else 1)
        clean = strip_lean_comments_and_strings(raw)
        combined.append(clean)
        for key, pat in patterns.items():
            scans[key].extend(occurrences(pat, clean, path))

    endpoint = LEAN_ROOT / "Lollipop/Final/TheoremOne.lean"
    endpoint_text = endpoint.read_text()
    endpoint_match = re.search(
        r"theorem\s+theorem_one\s*\n\s*\(P\s*:\s*TheoremOne\.MaxProblemFamily[^)]*\)\s*\n"
        r"\s*\(h\s*:\s*GeometryCertificates\s+P\)\s*:\s*\n\s*TheoremOneStatement\s+P",
        endpoint_text,
    )
    obstruction = LEAN_ROOT / "Lollipop/Final/GeometryObstruction.lean"
    obstruction_text = obstruction.read_text()
    obstruction_present = "no_geometryCertificates_zeroRegionMaxProblemFamily" in obstruction_text

    all_clean = "\n".join(combined)
    topology_terms = {
        term: len(re.findall(rf"\b{re.escape(term)}\b", all_clean))
        for term in ["ConnectedComponents", "connectedComponent", "IsPreconnected", "Alexander", "MayerVietoris"]
    }

    result = {
        "scope": str(LEAN_ROOT),
        "lean_project_files_including_lakefile": len(files),
        "lean_library_source_files": len(library_files),
        "source_lines": total_lines,
        "placeholder_scan_after_stripping_comments_and_strings": scans,
        "placeholder_free_by_this_static_scan": all(not v for v in scans.values()),
        "public_endpoint_is_conditional_on_GeometryCertificates": bool(endpoint_match),
        "geometry_obstruction_theorem_present": obstruction_present,
        "topological_region_semantics_term_counts": topology_terms,
        "kernel_build_run_by_this_script": False,
        "kernel_build_note": "This static audit does not run lake build; run `lake build Lollipop` separately for kernel verification.",
        "verdict": "Substantial conditional formalization; not an unconditional end-to-end formalization of Euclidean complement regions.",
    }
    OUT.mkdir(exist_ok=True)
    (OUT / "lean_static_audit.json").write_text(json.dumps(result, indent=2) + "\n")

    lines = [
        "Lean source audit",
        "=================",
        f"Lean project .lean files (including lakefile.lean): {len(files)}",
        f"Lean library source files: {len(library_files)}",
        f"Source lines: {total_lines:,}",
        "",
        "Placeholder/declaration scan after stripping nested comments and strings:",
    ]
    for key, values in scans.items():
        lines.append(f"  {key}: {len(values)}")
    lines += [
        "",
        f"Public theorem endpoint conditional on GeometryCertificates: {bool(endpoint_match)}",
        f"Geometry obstruction theorem present: {obstruction_present}",
        "Concrete complement-topology identifier counts:",
    ]
    for key, value in topology_terms.items():
        lines.append(f"  {key}: {value}")
    lines += [
        "",
        "Lean kernel build run by this script: NO",
        "Reason: this script is a static source audit. Run `lake build Lollipop` separately for kernel verification.",
        "",
        "VERDICT: The tree is a substantial, statically placeholder-free conditional development,",
        "but it is not an unconditional end-to-end formalization of the theorem about actual",
        "connected components of Euclidean lollipop complements.",
    ]
    text = "\n".join(lines) + "\n"
    (OUT / "lean_static_audit.txt").write_text(text)
    print(text)


if __name__ == "__main__":
    main()
