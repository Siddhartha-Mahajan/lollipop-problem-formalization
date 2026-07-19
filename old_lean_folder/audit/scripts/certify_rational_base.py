#!/usr/bin/env python3
"""Exact rational verification of the four-lollipop lower-bound base.

Every geometric input is rational.  All branching and all sign decisions use
fractions.Fraction; decimal strings are emitted only for readability after the
exact decisions have been made.
"""
from __future__ import annotations

from dataclasses import dataclass
from decimal import Decimal, localcontext
from fractions import Fraction as Q
from itertools import combinations
import json
from pathlib import Path
from typing import Dict, Iterable, Tuple

Vec = Tuple[Q, Q]


def add(x: Vec, y: Vec) -> Vec:
    return (x[0] + y[0], x[1] + y[1])


def sub(x: Vec, y: Vec) -> Vec:
    return (x[0] - y[0], x[1] - y[1])


def scale(a: Q | int, x: Vec) -> Vec:
    a = Q(a)
    return (a * x[0], a * x[1])


def dot(x: Vec, y: Vec) -> Q:
    return x[0] * y[0] + x[1] * y[1]


def norm2(x: Vec) -> Q:
    return dot(x, x)


def det(x: Vec, y: Vec) -> Q:
    return x[0] * y[1] - x[1] * y[0]


def qstr(x: Q) -> str:
    return str(x.numerator) if x.denominator == 1 else f"{x.numerator}/{x.denominator}"


def decstr(x: Q, digits: int = 18) -> str:
    with localcontext() as ctx:
        ctx.prec = digits + 10
        value = Decimal(x.numerator) / Decimal(x.denominator)
        return format(value, f".{digits}g")


def record(x: Q) -> Dict[str, str]:
    return {"exact": qstr(x), "decimal": decstr(x)}


@dataclass(frozen=True)
class Lollipop:
    name: str
    center: Vec
    radius: Q
    direction: Vec

    @property
    def anchor(self) -> Vec:
        return add(self.center, scale(self.radius, self.direction))


def from_anchor(name: str, anchor: Vec, radius: Q | int, direction: Vec) -> Lollipop:
    r = Q(radius)
    return Lollipop(name, sub(anchor, scale(r, direction)), r, direction)


def from_center(name: str, center: Vec, radius: Q | int, direction: Vec) -> Lollipop:
    return Lollipop(name, center, Q(radius), direction)


def require_pos(label: str, x: Q, checks: Dict[str, Dict[str, str]]) -> None:
    if x <= 0:
        raise AssertionError(f"{label}: expected positive, got {qstr(x)}")
    checks[label] = {"required_sign": "+", **record(x)}


def require_neg(label: str, x: Q, checks: Dict[str, Dict[str, str]]) -> None:
    if x >= 0:
        raise AssertionError(f"{label}: expected negative, got {qstr(x)}")
    checks[label] = {"required_sign": "-", **record(x)}


def classify_mixed(
    source: Lollipop,
    target: Lollipop,
    checks: Dict[str, Dict[str, str]],
    prefix: str,
) -> int:
    """Count source ray (parameter t >= source.radius) against target circle."""
    d = sub(target.center, source.center)
    p = dot(d, source.direction)
    d2 = norm2(d)
    discriminant = target.radius**2 - (d2 - p**2)
    anchor_power = d2 - 2 * source.radius * p + source.radius**2 - target.radius**2
    vertex_ahead = p - source.radius

    require_pos(f"{prefix}.line_discriminant", discriminant, checks)
    if anchor_power < 0:
        require_neg(f"{prefix}.anchor_power", anchor_power, checks)
        return 1
    require_pos(f"{prefix}.anchor_power", anchor_power, checks)
    if vertex_ahead > 0:
        require_pos(f"{prefix}.vertex_ahead", vertex_ahead, checks)
        return 2
    require_neg(f"{prefix}.vertex_ahead", vertex_ahead, checks)
    return 0


def verify_pair(first: Lollipop, second: Lollipop) -> Dict:
    checks: Dict[str, Dict[str, str]] = {}
    d = sub(second.center, first.center)
    d2 = norm2(d)
    require_pos("circle_circle.inner_margin", d2 - (first.radius - second.radius) ** 2, checks)
    require_pos("circle_circle.outer_margin", (first.radius + second.radius) ** 2 - d2, checks)

    first_mixed = classify_mixed(
        first, second, checks, f"ray_{first.name}_circle_{second.name}"
    )
    second_mixed = classify_mixed(
        second, first, checks, f"ray_{second.name}_circle_{first.name}"
    )

    denominator = det(first.direction, second.direction)
    if denominator > 0:
        require_pos("ray_ray.direction_determinant", denominator, checks)
    else:
        require_neg("ray_ray.direction_determinant", denominator, checks)

    # c_i + t_i u_i = c_j + t_j u_j.
    first_parameter = det(d, second.direction) / denominator
    second_parameter = det(d, first.direction) / denominator
    require_pos(
        f"ray_ray.{first.name}_parameter_minus_radius",
        first_parameter - first.radius,
        checks,
    )
    require_pos(
        f"ray_ray.{second.name}_parameter_minus_radius",
        second_parameter - second.radius,
        checks,
    )

    components = {
        "circle_circle": 2,
        f"ray_{first.name}_circle_{second.name}": first_mixed,
        f"ray_{second.name}_circle_{first.name}": second_mixed,
        "ray_ray": 1,
    }
    components["total"] = sum(components.values())
    return {"pair": [first.name, second.name], "components": components, "checks": checks}


def build_base() -> Tuple[Lollipop, ...]:
    # Three primitive Pythagorean directions and one coordinate direction.
    u0 = (Q(1), Q(0))
    u1 = (Q(144, 145), Q(-17, 145))
    u2 = (Q(-36, 85), Q(-77, 85))
    u3 = (Q(-17, 145), Q(144, 145))

    return (
        from_anchor("Q0", (Q(0), Q(0)), 200, u0),
        from_center("Q1", (Q(9, 20), Q(2, 5)), Q(11, 20), u1),
        from_anchor("Q2", (Q(23, 20), Q(13, 20)), 100, u2),
        from_anchor("Q3", (Q(21, 20), Q(-1, 20)), 100, u3),
    )


def iter_signed_checks(records: Iterable[Dict]) -> Iterable[Tuple[str, Q]]:
    for rec in records:
        pair_name = "-".join(rec["pair"])
        for label, datum in rec["checks"].items():
            yield f"{pair_name}.{label}", Q(datum["exact"])


def main() -> None:
    outdir = Path(__file__).resolve().parents[1] / "verification"
    outdir.mkdir(parents=True, exist_ok=True)

    base = build_base()
    unit_checks = {}
    for item in base:
        value = norm2(item.direction)
        if value != 1:
            raise AssertionError(f"{item.name} direction is not unit: {qstr(value)}")
        unit_checks[item.name] = record(value)

    records = [verify_pair(base[i], base[j]) for i, j in combinations(range(4), 2)]
    totals = [rec["components"]["total"] for rec in records]
    if totals != [5, 7, 7, 7, 7, 7]:
        raise AssertionError(f"unexpected totals: {totals}")

    all_abs = [(label, abs(value)) for label, value in iter_signed_checks(records)]
    smallest_label, smallest_value = min(all_abs, key=lambda item: item[1])

    geometry = {}
    for item in base:
        geometry[item.name] = {
            "center": [record(item.center[0]), record(item.center[1])],
            "anchor": [record(item.anchor[0]), record(item.anchor[1])],
            "radius": record(item.radius),
            "direction": [record(item.direction[0]), record(item.direction[1])],
        }

    result = {
        "method": "exact rational arithmetic using fractions.Fraction",
        "floating_point_used_for_decisions": False,
        "unit_direction_checks": unit_checks,
        "geometry": geometry,
        "pairs": records,
        "pair_totals": totals,
        "total_crossings": sum(totals),
        "smallest_absolute_decisive_value": {
            "label": smallest_label,
            **record(smallest_value),
        },
        "result": "PASSED",
    }

    json_path = outdir / "rational_base_verification.json"
    text_path = outdir / "rational_base_verification.txt"
    json_path.write_text(json.dumps(result, indent=2) + "\n")

    lines = [
        "Exact rational verification of the four-lollipop base",
        "======================================================",
        "All inputs, branches, and sign decisions use fractions.Fraction.",
        "",
    ]
    for rec in records:
        c = rec["components"]
        i, j = rec["pair"]
        lines.append(
            f"{i}-{j}: circle-circle {c['circle_circle']}, "
            f"ray {i}/circle {j} {c[f'ray_{i}_circle_{j}']}, "
            f"ray {j}/circle {i} {c[f'ray_{j}_circle_{i}']}, "
            f"ray-ray {c['ray_ray']}; total {c['total']}"
        )
    lines.extend(
        [
            "",
            f"Total crossings: {sum(totals)}",
            f"Smallest absolute decisive value: {qstr(smallest_value)} "
            f"({smallest_label})",
            "Every required inequality is strict.",
            "RESULT: PASSED",
        ]
    )
    text_path.write_text("\n".join(lines) + "\n")
    print("\n".join(lines))


if __name__ == "__main__":
    main()
