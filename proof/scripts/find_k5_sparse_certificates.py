"""
Find sparse dual certificates for the Step-3 marginals used in the k=5 proof.

Idea:
  Let A x = b be the exact length-14 linear system (x = length-14 cylinders).
  To certify a target marginal c^T x, find lambda with
      A^T lambda = c.
  Then for every solution x of A x = b:
      c^T x = lambda^T b.

This script searches sparse lambda vectors with L1 minimization (SciPy), then
converts to exact rational certificates with SymPy and prunes redundant rows.

Run from proof/:
  uv run --with sympy --with scipy python scripts/find_k5_sparse_certificates.py
"""

from __future__ import annotations

import itertools
from dataclasses import dataclass

import numpy as np
import sympy as sp
from scipy.optimize import linprog

from prove_k5_impossible import allowed_words, length7_distribution_in_terms_of_p_t, marginal


@dataclass(frozen=True)
class LinearRow:
    coeffs: tuple[int, ...]
    rhs: sp.Expr
    label: str


def build_length14_system(p: sp.Symbol, t: sp.Symbol) -> tuple[list[LinearRow], list[str], dict[str, int]]:
    dist7 = length7_distribution_in_terms_of_p_t(p, t)
    dist7_marginals = {m: marginal(dist7, m, start=0) for m in range(1, 8)}

    words14 = sorted(allowed_words(14))
    words13 = sorted(allowed_words(13))
    index14 = {word: i for i, word in enumerate(words14)}

    rows: list[LinearRow] = []

    rows.append(
        LinearRow(
            coeffs=tuple([1] * len(words14)),
            rhs=sp.Integer(1),
            label="norm",
        )
    )

    for word13 in words13:
        coeffs = [0] * len(words14)
        for word14, i in index14.items():
            if word14.startswith(word13):
                coeffs[i] += 1
            if word14.endswith(word13):
                coeffs[i] -= 1
        rows.append(LinearRow(coeffs=tuple(coeffs), rhs=sp.Integer(0), label=f"stat13:{word13}"))

    for m in range(1, 8):
        n = 9 - m
        if n < 1 or n > 7:
            continue
        for x, px in dist7_marginals[m].items():
            if px == 0:
                continue
            for y, py in dist7_marginals[n].items():
                if py == 0:
                    continue
                coeffs = [0] * len(words14)
                for g_bits in itertools.product("01", repeat=5):
                    g = "".join(g_bits)
                    word14 = x + g + y
                    idx = index14.get(word14)
                    if idx is not None:
                        coeffs[idx] += 1
                rows.append(
                    LinearRow(
                        coeffs=tuple(coeffs),
                        rhs=sp.expand(px * py),
                        label=f"split:{m}:{x}:{n}:{y}",
                    )
                )

    return rows, words14, index14


def target_vector(words14: list[str], prefix: str) -> list[int]:
    m = len(prefix)
    return [1 if word14.startswith(prefix) else 0 for word14 in words14]


def lp_support(rows: list[LinearRow], c: list[int]) -> list[int]:
    matrix_a = np.array([row.coeffs for row in rows], dtype=float)
    matrix_m = matrix_a.T
    num_rows = matrix_m.shape[1]

    lhs = np.hstack([matrix_m, -matrix_m])
    objective = np.ones(2 * num_rows)
    bounds = [(0, None)] * (2 * num_rows)

    result = linprog(
        objective,
        A_eq=lhs,
        b_eq=np.array(c, dtype=float),
        bounds=bounds,
        method="highs",
    )
    if not result.success:
        raise RuntimeError(f"L1 solve failed: {result.message}")

    lam = result.x[:num_rows] - result.x[num_rows:]
    return [i for i, value in enumerate(lam) if abs(value) > 1e-8]


def exact_coefficients(rows: list[LinearRow], support: list[int], c: list[int]) -> list[sp.Expr] | None:
    if not support:
        return None

    # sum_j lambda_j * row_j = c  <=>  R^T lambda = c
    matrix_r = sp.Matrix([[rows[row_idx].coeffs[col] for row_idx in support] for col in range(len(c))])
    vector_c = sp.Matrix(c)
    lam_symbols = sp.symbols(f"l0:{len(support)}")
    solution = sp.linsolve((matrix_r, vector_c), lam_symbols)
    solutions = list(solution)
    if not solutions:
        return None
    if len(solutions) != 1:
        raise RuntimeError("unexpected: multiple affine branches in exact coefficient solve")

    coeffs = list(solutions[0])
    parameters = sorted(
        {symbol for expr in coeffs for symbol in expr.free_symbols if symbol not in set(lam_symbols)},
        key=lambda symbol: symbol.name,
    )
    coeffs = [sp.nsimplify(expr.subs({param: 0 for param in parameters})) for expr in coeffs]

    check = [
        sp.simplify(sum(coeffs[i] * rows[support[i]].coeffs[col] for i in range(len(support))) - c[col])
        for col in range(len(c))
    ]
    if any(value != 0 for value in check):
        return None
    return coeffs


def prune_support(rows: list[LinearRow], support: list[int], c: list[int]) -> tuple[list[int], list[sp.Expr]]:
    current_support = list(support)
    while True:
        removed = False
        for idx in list(current_support):
            candidate_support = [row_idx for row_idx in current_support if row_idx != idx]
            coeffs = exact_coefficients(rows, candidate_support, c)
            if coeffs is not None:
                current_support = candidate_support
                removed = True
                break
        if not removed:
            break

    final_coeffs = exact_coefficients(rows, current_support, c)
    if final_coeffs is None:
        raise RuntimeError("unexpected: failed to recover exact coefficients after pruning")
    return current_support, final_coeffs


def rhs_expression(rows: list[LinearRow], support: list[int], coeffs: list[sp.Expr]) -> sp.Expr:
    return sp.simplify(sum(coeffs[i] * rows[support[i]].rhs for i in range(len(support))))


def coeff_summary(coeffs: list[sp.Expr]) -> tuple[int, int]:
    if not coeffs:
        return 1, 0
    denom_lcm = int(sp.ilcm(*[sp.denom(value) for value in coeffs]))
    scaled = [sp.Integer(denom_lcm) * value for value in coeffs]
    max_abs = int(max(abs(sp.Integer(v)) for v in scaled))
    return denom_lcm, max_abs


def main() -> None:
    p = sp.Symbol("p", real=True)
    t = sp.Symbol("t", real=True)
    rows, words14, _index14 = build_length14_system(p, t)

    needed_prefixes = [
        "100100101",
        "00101001001",
        "100100",
        "10100101001001",
        "10010010101",
        "101001001",
        "01010101001001",
        "100100100100",
        "01001001",
        "100100100",
        "01001001001",
        "10010010010101",
        "001001",
    ]

    print("Sparse certificates for Step-3 queried marginals (k=5):")
    print("system: 280 rows x 86 vars, rank 86")
    print()

    support_sizes: list[int] = []
    for prefix in needed_prefixes:
        c = target_vector(words14, prefix)
        initial_support = lp_support(rows, c)
        support, coeffs = prune_support(rows, initial_support, c)
        expr = sp.factor(sp.expand(rhs_expression(rows, support, coeffs)))
        denom_lcm, max_abs = coeff_summary(coeffs)
        support_sizes.append(len(support))
        print(f"P({prefix})")
        print(f"  support: {len(initial_support)} -> {len(support)} rows")
        print(f"  coeffs: denominator lcm = {denom_lcm}, max |integer coeff| = {max_abs}")
        print(f"  value: {expr}")

    print()
    support_sizes_sorted = sorted(support_sizes)
    print("Support-size summary:")
    print("  sorted:", support_sizes_sorted)
    print("  total :", sum(support_sizes_sorted))
    print("  max   :", max(support_sizes_sorted))
    print("  median:", support_sizes_sorted[len(support_sizes_sorted) // 2])


if __name__ == "__main__":
    main()
