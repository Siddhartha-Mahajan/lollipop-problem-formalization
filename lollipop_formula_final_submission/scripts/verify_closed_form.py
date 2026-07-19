#!/usr/bin/env python3
"""Independent exact checker for the closed forms for M(n), S(n), and a_L(n).

The checker uses integer arithmetic only.  It verifies the one-variable
minimum from Proposition 6.2 against the period-16 formula, confirms the
indicator/floor form, and checks the periodic optimal quadruples over a broad
range.  This is a reproducibility aid; the manuscript contains the symbolic
proof.
"""
from __future__ import annotations

import json
from pathlib import Path

DELTA = (0, 33, 36, 9, 16, 25, 4, 17, 32, 17, 4, 25, 16, 9, 36, 33)
EXCEPTIONAL = {1, 2, 8, 14, 15}
OFFSETS = (
    (0, 0, 0, 0),
    (0, 0, 0, 1),
    (0, 0, 1, 1),
    (0, 1, 1, 1),
    (1, 1, 1, 1),
    (1, 1, 1, 2),
    (1, 1, 2, 2),
    (1, 2, 2, 2),
    (1, 2, 2, 3),
    (1, 2, 3, 3),
    (2, 2, 3, 3),
    (2, 2, 3, 4),
    (2, 2, 4, 4),
    (2, 3, 4, 4),
    (2, 3, 4, 5),
    (2, 3, 5, 5),
)


def parity(value: int) -> int:
    return value & 1


def four_m(n: int, quadruple: tuple[int, int, int, int]) -> int:
    """Return 2*M for a labeled quadruple, as an integer."""
    a, b, c, d = quadruple
    assert min(quadruple) >= 0 and sum(quadruple) == n
    return 3 * (a * a + b * b + c * c + d * d) + 4 * a * b


def one_variable_m4(n: int) -> tuple[int, list[int]]:
    """Return 4*M and all minimizing p=a+b, using the one-variable formula."""
    values = [
        5 * p * p
        + 3 * (n - p) * (n - p)
        + parity(p)
        + 3 * parity(n - p)
        for p in range(n + 1)
    ]
    best = min(values)
    return best, [p for p, value in enumerate(values) if value == best]


def main(limit: int = 4096) -> None:
    root = Path(__file__).resolve().parents[1]
    outdir = root / "verification"
    outdir.mkdir(parents=True, exist_ok=True)

    checked = 0
    optimizer_checks = 0
    sample_rows = []

    for n in range(limit + 1):
        r = n % 16
        k = n // 16
        m4, minimizers = one_variable_m4(n)

        # M=(15 n^2 + delta_r)/32, so 4M=(15 n^2 + delta_r)/8.
        expected_numerator = 15 * n * n + DELTA[r]
        assert expected_numerator % 8 == 0
        expected_m4 = expected_numerator // 8
        assert m4 == expected_m4, (n, m4, expected_m4, minimizers)

        # The displayed periodic quadruple must attain the same objective.
        base = (3 * k, 3 * k, 5 * k, 5 * k)
        quad = tuple(base[i] + OFFSETS[r][i] for i in range(4))
        assert list(quad) == sorted(quad)
        assert m4 == 2 * four_m(n, quad), (n, quad, m4, four_m(n, quad))
        optimizer_checks += 1

        # S=(33 n^2-delta_r)/32 and the floor/indicator form agree.
        s_num = 33 * n * n - DELTA[r]
        assert s_num % 32 == 0
        s_value = s_num // 32
        floor_form = (33 * n * n) // 32 - int(r in EXCEPTIONAL)
        assert s_value == floor_form

        # Main lollipop formula in its two equivalent forms.
        regions_from_s = 4 * (n * (n - 1) // 2) + s_value + n + 1
        closed_regions = (97 * n * n) // 32 - n + 1 - int(r in EXCEPTIONAL)
        assert regions_from_s == closed_regions

        if n <= 20:
            sample_rows.append(
                {
                    "n": n,
                    "minimizing_p": minimizers,
                    "optimal_quadruple": quad,
                    "S": s_value,
                    "a_L": closed_regions,
                }
            )
        checked += 1

    result = {
        "method": "integer arithmetic only",
        "range_checked": [0, limit],
        "values_checked": checked,
        "periodic_optimizer_checks": optimizer_checks,
        "delta_by_residue": list(DELTA),
        "exceptional_residues": sorted(EXCEPTIONAL),
        "initial_values": sample_rows,
        "result": "PASSED",
    }
    (outdir / "closed_form_verification.json").write_text(
        json.dumps(result, indent=2) + "\n"
    )

    lines = [
        "Exact closed-form verification",
        "==============================",
        "All decisions use integer arithmetic.",
        f"Checked n = 0,...,{limit} ({checked} values).",
        f"Checked {optimizer_checks} periodic optimal quadruples.",
        "Verified M(n), S(n), the floor/indicator form, and the main region formula.",
        "RESULT: PASSED",
        "",
    ]
    text = "\n".join(lines)
    (outdir / "closed_form_verification.txt").write_text(text)
    print(text, end="")


if __name__ == "__main__":
    main()
