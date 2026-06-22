#!/usr/bin/env python3
"""Exact and numerical verification of the corrected local blow-up family.

The exact part checks every symbolic identity used in the manuscript with
SymPy.  The rational-grid part checks all interval inequalities with Fraction
arithmetic.  The numerical part computes the actual four primitive component
intersections for representative parameter pairs.
"""

from __future__ import annotations

import json
import math
from dataclasses import dataclass
from fractions import Fraction
from pathlib import Path
from typing import Iterable

import sympy as sp


@dataclass(frozen=True)
class Lollipop:
    center: tuple[float, float]
    radius: float
    vector: tuple[float, float]

    @property
    def anchor(self) -> tuple[float, float]:
        return (self.center[0] + self.vector[0], self.center[1] + self.vector[1])


def family(t: float) -> Lollipop:
    return Lollipop((3.0 * t, 3.0 * t), 1.0 + t * t, (1.0 - t * t, -2.0 * t))


def add(a: tuple[float, float], b: tuple[float, float]) -> tuple[float, float]:
    return (a[0] + b[0], a[1] + b[1])


def sub(a: tuple[float, float], b: tuple[float, float]) -> tuple[float, float]:
    return (a[0] - b[0], a[1] - b[1])


def scale(x: float, a: tuple[float, float]) -> tuple[float, float]:
    return (x * a[0], x * a[1])


def dot(a: tuple[float, float], b: tuple[float, float]) -> float:
    return a[0] * b[0] + a[1] * b[1]


def det(a: tuple[float, float], b: tuple[float, float]) -> float:
    return a[0] * b[1] - a[1] * b[0]


def norm2(a: tuple[float, float]) -> float:
    return dot(a, a)


def circle_circle_points(a: Lollipop, b: Lollipop) -> list[tuple[float, float]]:
    dvec = sub(b.center, a.center)
    d = math.sqrt(norm2(dvec))
    if not (abs(a.radius - b.radius) < d < a.radius + b.radius):
        return []
    x = (a.radius * a.radius - b.radius * b.radius + d * d) / (2.0 * d)
    h2 = a.radius * a.radius - x * x
    if h2 <= 0.0:
        return []
    h = math.sqrt(h2)
    u = scale(1.0 / d, dvec)
    p = add(a.center, scale(x, u))
    perp = (-u[1], u[0])
    return [add(p, scale(h, perp)), add(p, scale(-h, perp))]


def ray_circle_points(ray: Lollipop, circle: Lollipop) -> list[tuple[float, float]]:
    # Center-based ray parameter q >= 1.
    w = sub(ray.center, circle.center)
    aa = norm2(ray.vector)
    bb = 2.0 * dot(w, ray.vector)
    cc = norm2(w) - circle.radius * circle.radius
    disc = bb * bb - 4.0 * aa * cc
    if disc < -1e-12:
        return []
    disc = max(0.0, disc)
    roots = [(-bb - math.sqrt(disc)) / (2.0 * aa), (-bb + math.sqrt(disc)) / (2.0 * aa)]
    accepted: list[tuple[float, float]] = []
    for q in roots:
        if q >= 1.0 - 1e-10:
            p = add(ray.center, scale(q, ray.vector))
            if not any(norm2(sub(p, old)) < 1e-18 for old in accepted):
                accepted.append(p)
    return accepted


def ray_ray_points(a: Lollipop, b: Lollipop) -> list[tuple[float, float]]:
    denominator = det(a.vector, b.vector)
    if abs(denominator) < 1e-14:
        return []
    delta = sub(b.center, a.center)
    lam = det(delta, b.vector) / denominator
    mu = det(delta, a.vector) / denominator
    if lam >= 1.0 - 1e-10 and mu >= 1.0 - 1e-10:
        pa = add(a.center, scale(lam, a.vector))
        pb = add(b.center, scale(mu, b.vector))
        assert norm2(sub(pa, pb)) < 1e-16
        return [pa]
    return []


def symbolic_checks() -> dict[str, str]:
    s, t, q = sp.symbols("s t q", real=True)
    cs = sp.Matrix([3 * s, 3 * s])
    ct = sp.Matrix([3 * t, 3 * t])
    vs = sp.Matrix([1 - s**2, -2 * s])
    vt = sp.Matrix([1 - t**2, -2 * t])
    rs = 1 + s**2
    rt = 1 + t**2

    radial = sp.expand((1 - t**2) ** 2 + 4 * t**2 - (1 + t**2) ** 2)
    assert radial == 0

    f = sp.expand((cs + q * vs - ct).dot(cs + q * vs - ct) - rt**2)
    g = sp.expand((ct + q * vt - cs).dot(ct + q * vt - cs) - rs**2)
    b = 6 + 8 * s - 16 * t - 6 * s**2 + s**3 + s**2 * t + s * t**2 + t**3
    c = 6 - 16 * s + 8 * t - 6 * t**2 + s**3 + s**2 * t + s * t**2 + t**3
    assert sp.expand(f.subs(q, 1) + (t - s) * b) == 0
    assert sp.expand(g.subs(q, 1) - (t - s) * c) == 0

    fhalf = (1 + s**2) ** 2 - 3 * (t - s) * (1 - 2 * s - s**2)
    ghalf = (1 + t**2) ** 2 + 3 * (t - s) * (1 - 2 * t - t**2)
    assert sp.expand(sp.diff(f, q).subs(q, 1) / 2 - fhalf) == 0
    assert sp.expand(sp.diff(g, q).subs(q, 1) / 2 - ghalf) == 0

    determinant = sp.det(sp.Matrix.hstack(vs, vt))
    assert sp.expand(determinant - 2 * (s - t) * (1 + s * t)) == 0

    lam = 3 * (1 + 2 * t - t**2) / (2 * (1 + s * t))
    mu = 3 * (1 + 2 * s - s**2) / (2 * (1 + s * t))
    residual = sp.simplify(cs + lam * vs - ct - mu * vt)
    assert residual == sp.zeros(2, 1)

    return {
        "radial_identity": "exact",
        "F_anchor_factorization": "exact",
        "G_anchor_factorization": "exact",
        "F_derivative_identity": "exact",
        "G_derivative_identity": "exact",
        "direction_determinant": "exact",
        "ray_ray_solution": "exact",
    }


def fraction_pair_check(s: Fraction, t: Fraction) -> None:
    assert Fraction(0) <= s < t <= Fraction(1, 4)
    delta = t - s

    center_sq = 18 * delta * delta
    diff_sq = delta * delta * (s + t) * (s + t)
    sum_sq = (2 + s * s + t * t) ** 2
    assert diff_sq < center_sq < sum_sq

    b = 6 + 8 * s - 16 * t - 6 * s**2 + s**3 + s**2 * t + s * t**2 + t**3
    c = 6 - 16 * s + 8 * t - 6 * t**2 + s**3 + s**2 * t + s * t**2 + t**3
    assert b >= Fraction(13, 8)
    assert c > Fraction(29, 8)
    assert -delta * b < 0
    assert delta * c > 0

    fhalf = (1 + s**2) ** 2 - 3 * delta * (1 - 2 * s - s**2)
    ghalf = (1 + t**2) ** 2 + 3 * delta * (1 - 2 * t - t**2)
    assert fhalf >= Fraction(1, 4)
    assert ghalf > 0

    determinant = 2 * (s - t) * (1 + s * t)
    assert determinant != 0
    lam = 3 * (1 + 2 * t - t**2) / (2 * (1 + s * t))
    mu = 3 * (1 + 2 * s - s**2) / (2 * (1 + s * t))
    assert lam > 1
    assert mu > 1


def exact_grid_checks(denominator: int = 256) -> int:
    upper = denominator // 4
    pairs = 0
    for i in range(upper + 1):
        for j in range(i + 1, upper + 1):
            fraction_pair_check(Fraction(i, denominator), Fraction(j, denominator))
            pairs += 1
    return pairs


def numerical_component_check(s: float, t: float) -> dict[str, object]:
    assert 0.0 <= s < t <= 0.25
    a, b = family(s), family(t)
    components = {
        "circle_circle": circle_circle_points(a, b),
        "ray_s_circle_t": ray_circle_points(a, b),
        "ray_t_circle_s": ray_circle_points(b, a),
        "ray_ray": ray_ray_points(a, b),
    }
    counts = {name: len(points) for name, points in components.items()}
    assert counts == {
        "circle_circle": 2,
        "ray_s_circle_t": 1,
        "ray_t_circle_s": 0,
        "ray_ray": 1,
    }
    all_points = [p for points in components.values() for p in points]
    for i, p in enumerate(all_points):
        for q in all_points[i + 1 :]:
            assert norm2(sub(p, q)) > 1e-14
    return {
        "s": s,
        "t": t,
        "counts": counts,
        "total": len(all_points),
        "points": [[round(x, 12), round(y, 12)] for x, y in all_points],
    }


def main() -> None:
    root = Path(__file__).resolve().parents[1]
    report_dir = root / "verification"
    report_dir.mkdir(parents=True, exist_ok=True)

    symbolic = symbolic_checks()
    grid_pairs = exact_grid_checks()
    samples = [
        numerical_component_check(0.0, 0.01),
        numerical_component_check(0.03, 0.17),
        numerical_component_check(0.125, 0.25),
    ]

    data = {
        "symbolic_checks": symbolic,
        "exact_fraction_grid_denominator": 256,
        "exact_fraction_pairs_checked": grid_pairs,
        "numerical_samples": samples,
        "result": "passed",
    }
    (report_dir / "verification_report.json").write_text(json.dumps(data, indent=2) + "\n")

    lines = [
        "Corrected polynomial blow-up verification",
        "=========================================",
        "",
        f"Symbolic identities checked exactly: {len(symbolic)}",
        f"Exact rational parameter pairs checked: {grid_pairs}",
        "Expected primitive component vector: 2 + 1 + 0 + 1 = 4",
        "",
    ]
    for sample in samples:
        lines.append(
            f"s={sample['s']}, t={sample['t']}: {sample['counts']}, total={sample['total']}"
        )
    lines.extend(["", "RESULT: PASSED", ""])
    text = "\n".join(lines)
    (report_dir / "verification_report.txt").write_text(text)
    print(text)


if __name__ == "__main__":
    main()
