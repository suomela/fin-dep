"""
Proof script (computer-assisted, exact) that no stationary 5-dependent MIS exists on Z.

MIS indicator process on Z = {0,1}-process forbidding '11' and '000'.

Important historical note:
  An earlier version of this repo claimed an impossibility proof for k=5 via two
  "bounds" on a free parameter t := P(1010101). That argument was **wrong**:
  it implicitly linearized in t (effectively assuming t^2=t). In reality, a key
  length-15 word probability is quadratic in t.

Current proof idea:
  1) Stationarity + 5-dependence force a 2-parameter affine family of length-7
     cylinders in terms of:
        p := P(X0=1),  t := P(1010101).
  2) Solvability of the length-11 extension system forces the length-10 free
     parameter u := P(1010100101) to equal:
        u = 3 p^2 - 5 p + t + 3/2.
     (This is computed exactly by linear algebra.)
  3) Build two fixed linear systems with known RHS from length-15 marginals:
        length 16: 727 rows, 151 vars,
        length 20: 3002 rows, 465 vars.
     Sparse row-combination certificates give compatibility residuals
     f(p,t)=0 and r(p,t)=0.
  4) Set g := 3f + r.  This is linear in t, so solving g=0 for t and
     substituting into f yields
       A(p)B(p)=0
     with explicit quartics A and B.
  5) A sparse Step-4 certificate gives a third compatibility polynomial q(p,t)=0
     directly from length-15 marginals:
       - two length-19 split rows determine P(0010101010010010100),
       - two length-25 split rows determine P(0101010010101010010010100),
       - and three length-25 split rows ((A),(B),(W)) eliminate the remaining
         length-25 unknowns.
     This yields q(p,t)=0 with no large linear solve.
  6) Eliminating t via g=0 gives two necessary univariate constraints:
       A(p)B(p)=0  (from f),
       P12(p)=0    (from q),
     and gcd(A,P12)=gcd(B,P12)=1, contradiction.

Run:
  # rigorous certificate path (default)
  uv run --with sympy python scripts/prove_k5_impossible.py

  # deeper exact audit (rebuilds Step-2 fixed systems)
  uv run --with sympy python scripts/prove_k5_impossible.py --full-audit
"""

from __future__ import annotations

import argparse
import itertools
from dataclasses import dataclass

import sympy as sp
from sympy import QQ
from sympy.polys.matrices import DomainMatrix


def allowed_mis(word: str) -> bool:
    return "11" not in word and "000" not in word


def allowed_words(L: int) -> list[str]:
    if L < 0:
        raise ValueError("L must be >= 0")
    if L == 0:
        return [""]
    words = ["0", "1"]
    while len(words[0]) < L:
        out: list[str] = []
        for w in words:
            if w.endswith("1"):
                out.append(w + "0")
            elif w.endswith("00"):
                out.append(w + "1")
            else:
                out.append(w + "0")
                out.append(w + "1")
        words = out
    return words


def marginal(dist: dict[str, sp.Expr], m: int, start: int = 0) -> dict[str, sp.Expr]:
    out: dict[str, sp.Expr] = {}
    for w, prob in dist.items():
        sub = w[start : start + m]
        out[sub] = out.get(sub, 0) + prob
    return out


def solve_next(dist_prev: dict[str, sp.Expr], k: int) -> dict[str, sp.Expr]:
    L_prev = len(next(iter(dist_prev)))
    L = L_prev + 1
    W = sorted(allowed_words(L))

    vars = [sp.Symbol("P" + w) for w in W]
    idx = {w: i for i, w in enumerate(W)}

    eqs: list[sp.Expr] = []
    eqs.append(sum(vars) - 1)

    for u, val in dist_prev.items():
        eqs.append(sum(vars[idx[w]] for w in W if w.startswith(u)) - val)
        eqs.append(sum(vars[idx[w]] for w in W if w.endswith(u)) - val)

    P = {L_prev: dist_prev}
    for m in range(1, L_prev):
        P[m] = marginal(dist_prev, m, start=0)

    gap = k
    for m in range(1, L):
        n = L - gap - m
        if n < 1:
            continue
        Pm = P[m]
        Pn = P[n]
        for x, px in Pm.items():
            if px == 0:
                continue
            for y, py in Pn.items():
                if py == 0:
                    continue
                rhs = sp.simplify(px * py)
                lhs = 0
                for g_bits in itertools.product("01", repeat=gap):
                    g = "".join(g_bits)
                    w = x + g + y
                    if w in idx:
                        lhs += vars[idx[w]]
                eqs.append(lhs - rhs)

    eqs = [sp.simplify(e) for e in eqs if sp.simplify(e) != 0]
    sol = sp.linsolve(eqs, vars)
    sols = list(sol)
    if len(sols) != 1:
        raise RuntimeError(f"unexpected: extension solution set size {len(sols)} at L={L}")
    vec = sols[0]
    return {w: sp.simplify(vec[i]) for i, w in enumerate(W)}


def length7_distribution_closed_form(p: sp.Symbol, t: sp.Symbol) -> dict[str, sp.Expr]:
    """
    Closed-form length-7 family from the manuscript (Step 1), indexed by admissible words.
    """
    dist7 = {
        "0010010": p**2 - t,
        "0010100": -2 * p**2 - 7 * p + 3 * t + 3,
        "0010101": p**2 + 5 * p - 2 * t - 2,
        "0100100": p**2 - t,
        "0100101": -p**2 - 2 * p + t + 1,
        "0101001": -p**2 - 2 * p + t + 1,
        "0101010": p**2 + 5 * p - t - 2,
        "1001001": p**2 - t,
        "1001010": -p**2 - 2 * p + t + 1,
        "1010010": -p**2 - 2 * p + t + 1,
        "1010100": p**2 + 5 * p - 2 * t - 2,
        "1010101": t,
    }
    if sorted(dist7) != sorted(allowed_words(7)):
        raise RuntimeError("unexpected: length-7 support mismatch")
    return {w: sp.expand(expr) for w, expr in dist7.items()}


def verify_length7_constraints(dist7: dict[str, sp.Expr], p: sp.Symbol) -> None:
    """
    Verify that a proposed length-7 family satisfies the Step-1 constraints:
    normalization, stationarity on length 6, one-site marginal, and X0 ⟂ X6.
    """
    W7 = sorted(allowed_words(7))
    W6 = sorted(allowed_words(6))
    if sorted(dist7) != W7:
        raise RuntimeError("unexpected: length-7 keys do not match admissible words")

    if sp.simplify(sum(dist7.values()) - 1) != 0:
        raise RuntimeError("length-7 closed form failed normalization")

    for u in W6:
        lhs = sum(dist7[w] for w in W7 if w.startswith(u))
        rhs = sum(dist7[w] for w in W7 if w.endswith(u))
        if sp.simplify(lhs - rhs) != 0:
            raise RuntimeError(f"length-7 closed form failed stationarity at u={u}")

    if sp.simplify(sum(dist7[w] for w in W7 if w[0] == "1") - p) != 0:
        raise RuntimeError("length-7 closed form failed one-site marginal")

    P1 = {"0": 1 - p, "1": p}
    for a in "01":
        for b in "01":
            lhs = sum(dist7[w] for w in W7 if w[0] == a and w[-1] == b)
            rhs = sp.expand(P1[a] * P1[b])
            if sp.simplify(lhs - rhs) != 0:
                raise RuntimeError(f"length-7 closed form failed independence at ({a},{b})")


def length7_distribution_in_terms_of_p_t(p: sp.Symbol, t: sp.Symbol) -> dict[str, sp.Expr]:
    """
    Solve the length-7 linear constraints in terms of:
      p = P(X0=1),
      t = P(1010101).
    """
    L = 7
    W7 = sorted(allowed_words(L))
    W6 = sorted(allowed_words(L - 1))
    vars7 = [sp.Symbol("P" + w) for w in W7]
    idx = {w: i for i, w in enumerate(W7)}

    P1 = {"0": 1 - p, "1": p}

    eqs: list[sp.Expr] = []
    eqs.append(sum(vars7) - 1)

    # stationarity on length 6
    for u in W6:
        eqs.append(
            sum(vars7[idx[w]] for w in W7 if w.startswith(u))
            - sum(vars7[idx[w]] for w in W7 if w.endswith(u))
        )

    # one-site marginal
    eqs.append(sum(vars7[idx[w]] for w in W7 if w[0] == "1") - p)

    # 5-dependence implies X0 is independent of X6 (distance 6 > 5)
    for a in "01":
        for b in "01":
            lhs = sum(vars7[idx[w]] for w in W7 if w[0] == a and w[-1] == b)
            rhs = sp.simplify(P1[a] * P1[b])
            eqs.append(lhs - rhs)

    eqs = [sp.simplify(e) for e in eqs if sp.simplify(e) != 0]
    sol = sp.linsolve(eqs, vars7)
    sols = list(sol)
    if len(sols) != 1:
        raise RuntimeError(f"unexpected: length-7 solution set size {len(sols)}")
    vec = sols[0]

    # The unique free parameter is P1010101.
    u = sp.Symbol("P1010101")
    dist7 = {w: sp.simplify(vec[i]) for i, w in enumerate(W7)}
    if dist7["1010101"] != u:
        raise RuntimeError("unexpected: did not get P1010101 as the free parameter")

    # Rename u -> t.
    dist7 = {w: sp.simplify(expr.subs({u: t})) for w, expr in dist7.items()}

    # Sanity checks: normalization and that the parameter is t.
    if sp.simplify(sum(dist7.values())) != 1:
        raise RuntimeError("unexpected: length-7 distribution does not normalize to 1")
    if sp.simplify(dist7["1010101"] - t) != 0:
        raise RuntimeError("unexpected: parameter rename failed")

    return dist7


def dist15_in_terms_of_p_t(p: sp.Symbol, t: sp.Symbol) -> dict[str, sp.Expr]:
    """
    Forced length-15 distribution as expressions in (p,t).

    This uses:
      - the length-7 affine family in (p,t), and
      - the forced length-10 parameter
            u := P(1010100101) = 3 p^2 - 5 p + t + 3/2
        obtained from solvability at length 11.
    """
    dist = length7_distribution_in_terms_of_p_t(p, t)

    for L in range(8, 11):
        dist = solve_next(dist, k=5)
        if L == 10:
            u_sym = sp.Symbol("P1010100101")
            u_val = sp.simplify(3 * p**2 - 5 * p + t + sp.Rational(3, 2))
            dist = {w: sp.simplify(v.subs({u_sym: u_val})) for w, v in dist.items()}

    for _L in range(11, 16):
        dist = solve_next(dist, k=5)

    return dist


@dataclass(frozen=True)
class FixedSystem:
    L: int
    W: list[str]
    A: DomainMatrix
    rhs_expr: list[sp.Expr]
    row_labels: list[tuple[str, object]]


# Sparse split-row certificates used in Step 2.
# Each entry is (row_label, coefficient), where row_label = ("split", (m, x, n, y)).
CERT_F: list[tuple[tuple[str, object], int]] = [
    (("split", (1, "1", 10, "0010100101")), 1),
    (("split", (3, "100", 8, "10100101")), -1),
    (("split", (5, "10100", 6, "001001")), 1),
    (("split", (5, "10100", 6, "100101")), -1),
    (("split", (6, "100100", 5, "00101")), 1),
    (("split", (8, "10100101", 3, "101")), 1),
    (("split", (10, "1010010101", 1, "1")), -1),
]

CERT_R: list[tuple[tuple[str, object], int]] = [
    (("split", (5, "00100", 10, "1010010100")), -1),
    (("split", (8, "00100100", 7, "0010100")), 1),
    (("split", (10, "0010010100", 5, "10100")), 1),
    (("split", (13, "0010010100100", 2, "00")), -1),
]

# Sparse rows used in the new Step-4 compatibility certificate.
STEP4_L19_ANCHOR = (2, "00", 12, "001010010100")
STEP4_L19_EDGE = (7, "0010101", 7, "0010100")
STEP4_L25_S_ANCHOR = (8, "01010100", 12, "001010010100")
STEP4_L25_S_EDGE = (13, "0101010010101", 7, "0010100")
STEP4_L25_A = (1, "0", 19, "0010101010010010100")
STEP4_L25_B = (5, "00100", 15, "101010010010100")
STEP4_L25_W = (10, "0010010100", 10, "0010010100")

def split_support_words(L: int, m: int, x: str, n: int, y: str, gap: int = 5) -> list[str]:
    if m + gap + n != L:
        raise RuntimeError(f"split ({m},{x};{n},{y}) does not match length {L}")
    words_L = allowed_words(L)
    out: list[str] = []
    for w in words_L:
        if w.startswith(x) and w[m + gap :] == y:
            out.append(w)
    return out


def certificate_rhs_terms_from_dist15(
    cert: list[tuple[tuple[str, object], int]], dist15: dict[str, sp.Expr]
) -> list[sp.Expr]:
    marg15 = {m: marginal(dist15, m, start=0) for m in range(1, 16)}
    rhs_terms: list[sp.Expr] = []
    for label, _coeff in cert:
        kind, data = label
        if kind != "split":
            raise RuntimeError(f"unexpected non-split certificate row label: {label!r}")
        m, x, n, y = data
        if m < 1 or n < 1 or m > 15 or n > 15:
            raise RuntimeError(f"certificate row out of supported range m,n <= 15: {label!r}")
        rhs_terms.append(sp.expand(marg15[m].get(x, 0) * marg15[n].get(y, 0)))
    return rhs_terms


def verify_certificate_lhs_cancellation(
    cert: list[tuple[tuple[str, object], int]], L: int, name: str
) -> int:
    coeff_by_word: dict[str, int] = {}
    total_terms = 0
    for label, coeff in cert:
        kind, data = label
        if kind != "split":
            raise RuntimeError(f"{name}: unexpected non-split certificate row label: {label!r}")
        m, x, n, y = data
        support = split_support_words(L=L, m=m, x=x, n=n, y=y, gap=5)
        if not support:
            raise RuntimeError(f"{name}: split row has empty support: {label!r}")
        total_terms += len(support)
        for w in support:
            coeff_by_word[w] = coeff_by_word.get(w, 0) + coeff

    bad = {w: c for w, c in coeff_by_word.items() if c != 0}
    if bad:
        raise RuntimeError(f"{name}: certificate LHS does not cancel; nonzero words: {bad}")
    return total_terms


def certificate_from_dist15(
    cert: list[tuple[tuple[str, object], int]], dist15: dict[str, sp.Expr], L: int, name: str
) -> sp.Expr:
    """
    Verify a sparse split-row certificate directly:
      - combinatorial LHS cancellation on length-L words,
      - RHS computed from exact length-15 marginals.
    """
    rhs_terms = certificate_rhs_terms_from_dist15(cert, dist15)
    total_terms = verify_certificate_lhs_cancellation(cert, L=L, name=name)

    poly = sp.Integer(0)
    print(f"\n{name} certificate:")
    print(f"  rows used: {len(cert)}")
    print(f"  split-word terms before cancellation: {total_terms}")
    print("  labels and coefficients:")
    for (label, coeff), rhs in zip(cert, rhs_terms, strict=True):
        print(f"    {coeff:+d} * {label}")
        poly += sp.Integer(coeff) * rhs
    poly = sp.factor(sp.expand(poly))
    print(f"  polynomial: {poly}")
    return poly


def split_rhs_from_marg15(
    marg15: dict[int, dict[str, sp.Expr]], data: tuple[int, str, int, str], name: str
) -> sp.Expr:
    m, x, n, y = data
    if m < 1 or n < 1 or m > 15 or n > 15:
        raise RuntimeError(f"{name}: split RHS requires marginals outside length 15: {data}")
    return sp.expand(marg15[m].get(x, 0) * marg15[n].get(y, 0))


def verify_split_support_exact(
    L: int, data: tuple[int, str, int, str], expected: set[str], name: str
) -> None:
    m, x, n, y = data
    support = set(split_support_words(L=L, m=m, x=x, n=n, y=y, gap=5))
    if support != expected:
        raise RuntimeError(f"{name}: unexpected split support {sorted(support)} (expected {sorted(expected)})")


def step4_sparse_polynomial_from_dist15(dist15: dict[str, sp.Expr], p: sp.Symbol, t: sp.Symbol) -> sp.Expr:
    """
    Step-4 sparse certificate:
      - two length-19 rows derive Y19 := P(0010101010010010100),
      - two length-25 rows derive S25 := P(0101010010101010010010100),
      - three length-25 rows (A,B,W) eliminate A25,T25 and force q(p,t)=0.

    All RHS terms are products of marginals of length <= 15.
    """
    marg15 = {m: marginal(dist15, m, start=0) for m in range(1, 16)}

    y_aux = "0010101001010010100"
    y19 = "0010101010010010100"
    s_aux = "0101010010101001010010100"
    s25 = "0101010010101010010010100"
    a25 = "0010010010101010010010100"
    t25 = "0010010100101010010010100"

    verify_split_support_exact(19, STEP4_L19_ANCHOR, {y_aux}, "step4-L19-anchor")
    verify_split_support_exact(19, STEP4_L19_EDGE, {y_aux, y19}, "step4-L19-edge")
    verify_split_support_exact(25, STEP4_L25_S_ANCHOR, {s_aux}, "step4-L25-S-anchor")
    verify_split_support_exact(25, STEP4_L25_S_EDGE, {s_aux, s25}, "step4-L25-S-edge")
    verify_split_support_exact(25, STEP4_L25_A, {a25, s25}, "step4-L25-A")
    verify_split_support_exact(25, STEP4_L25_B, {a25, t25}, "step4-L25-B")
    verify_split_support_exact(25, STEP4_L25_W, {t25}, "step4-L25-W")

    y19_expr = sp.expand(
        split_rhs_from_marg15(marg15, STEP4_L19_EDGE, "step4-L19-edge")
        - split_rhs_from_marg15(marg15, STEP4_L19_ANCHOR, "step4-L19-anchor")
    )
    s25_expr = sp.expand(
        split_rhs_from_marg15(marg15, STEP4_L25_S_EDGE, "step4-L25-S-edge")
        - split_rhs_from_marg15(marg15, STEP4_L25_S_ANCHOR, "step4-L25-S-anchor")
    )

    rhsA = sp.expand((1 - p) * y19_expr)
    rhsB = split_rhs_from_marg15(marg15, STEP4_L25_B, "step4-L25-B")
    rhsW = split_rhs_from_marg15(marg15, STEP4_L25_W, "step4-L25-W")

    residual = sp.expand((rhsB - rhsW) - (rhsA - s25_expr))
    q = sp.expand(-4 * residual)

    q_expected = sp.expand(
        4 * p**6
        + 64 * p**5
        - 12 * p**4 * t
        + 528 * p**4
        - 240 * p**3 * t
        + 80 * p**3
        + 12 * p**2 * t**2
        - 576 * p**2 * t
        - 552 * p**2
        + 180 * p * t**2
        + 540 * p * t
        + 260 * p
        - 4 * t**3
        - 72 * t**2
        - 108 * t
        - 35
    )
    if sp.expand(q - q_expected) != 0:
        raise RuntimeError("unexpected: Step-4 sparse polynomial mismatch")

    print("\nStep-4 sparse certificates:")
    print("  Y19 from two length-19 rows:")
    print(f"    split {STEP4_L19_ANCHOR}: P({y_aux}) = RHS")
    print(f"    split {STEP4_L19_EDGE}: P({y_aux}) + P({y19}) = RHS")
    print("  S25 from two length-25 rows:")
    print(f"    split {STEP4_L25_S_ANCHOR}: P({s_aux}) = RHS")
    print(f"    split {STEP4_L25_S_EDGE}: P({s_aux}) + P({s25}) = RHS")
    print("  Final elimination rows at length 25:")
    print(f"    split {STEP4_L25_A}: P({a25}) + P({s25}) = (1-p) * P({y19})")
    print(f"    split {STEP4_L25_B}: P({a25}) + P({t25}) = RHS")
    print(f"    split {STEP4_L25_W}: P({t25}) = RHS")
    print("  resulting q(p,t) =", sp.factor(q))

    return q


def qq_as_sympy(val) -> sp.Rational:
    """
    Convert a SymPy domain element (typically `PythonMPQ`) to a SymPy `Rational`.

    The sparse matrix reps (`SDM.to_dod()`) store domain elements directly.
    """
    if hasattr(val, "element"):  # DomainScalar
        val = val.element
    return sp.Rational(val.numerator, val.denominator)


def build_fixed_system_from_dist15(L: int, dist15: dict[str, sp.Expr]) -> FixedSystem:
    """
    Build a fixed system at length L with unknowns = length-L cylinders.

    Rows:
      0) normalization
      1.. ) stationarity on length-(L-1) words
      ... ) split equations with gap 5 and m+n=L-5, using marginals from dist15
            whenever m,n <= 15.
    """
    if L < 2:
        raise ValueError("L must be >= 2")
    words_L = allowed_words(L)
    words_Lm1 = allowed_words(L - 1)
    idx = {w: i for i, w in enumerate(words_L)}

    marg15 = {m: marginal(dist15, m, start=0) for m in range(1, 16)}

    rows: list[dict[int, object]] = []
    rhs_expr: list[sp.Expr] = []
    row_labels: list[tuple[str, object]] = []

    rows.append({j: QQ(1) for j in range(len(words_L))})
    rhs_expr.append(sp.Integer(1))
    row_labels.append(("norm", None))

    for u in words_Lm1:
        coeff: dict[int, object] = {}
        for w, j in idx.items():
            if w.startswith(u):
                coeff[j] = coeff.get(j, QQ(0)) + QQ(1)
            if w.endswith(u):
                coeff[j] = coeff.get(j, QQ(0)) - QQ(1)
        coeff = {j: v for j, v in coeff.items() if v != 0}
        rows.append(coeff)
        rhs_expr.append(sp.Integer(0))
        row_labels.append(("stat", u))

    for m in range(1, L):
        n = L - 5 - m
        if m < 1 or n < 1 or m > 15 or n > 15:
            continue
        for x, px in marg15[m].items():
            for y, py in marg15[n].items():
                coeff: dict[int, object] = {}
                for g_bits in itertools.product("01", repeat=5):
                    g = "".join(g_bits)
                    w = x + g + y
                    j = idx.get(w)
                    if j is not None:
                        coeff[j] = coeff.get(j, QQ(0)) + QQ(1)
                if not coeff:
                    continue
                rows.append(coeff)
                rhs_expr.append(sp.expand(px * py))
                row_labels.append(("split", (m, x, n, y)))

    A = DomainMatrix.from_dod({i: rows[i] for i in range(len(rows))}, (len(rows), len(words_L)), QQ)
    return FixedSystem(L=L, W=words_L, A=A, rhs_expr=rhs_expr, row_labels=row_labels)


def certificate_polynomial(system: FixedSystem, cert: list[tuple[tuple[str, object], int]], name: str) -> sp.Expr:
    """
    Verify a sparse certificate on a fixed system.

    Certificate condition:
      sum_i a_i * row_i = 0  on LHS (row-space cancellation),
    and then the same combination of RHS gives the compatibility polynomial.
    """
    label_to_index = {label: i for i, label in enumerate(system.row_labels)}
    selected: list[tuple[int, int]] = []
    for label, coeff in cert:
        idx = label_to_index.get(label)
        if idx is None:
            raise RuntimeError(f"{name}: certificate row label not found: {label!r}")
        selected.append((idx, coeff))

    lhs = [sp.Integer(0)] * len(system.W)
    A_dod = system.A.rep.to_dod()
    total_terms = 0
    for idx, coeff in selected:
        row_terms = 0
        for col, val in A_dod.get(idx, {}).items():
            lhs[col] += coeff * qq_as_sympy(val)
            row_terms += 1
        total_terms += row_terms

    if any(sp.simplify(v) != 0 for v in lhs):
        raise RuntimeError(f"{name}: certificate LHS does not cancel to zero")

    poly = sp.factor(sp.expand(sum(sp.Integer(coeff) * system.rhs_expr[idx] for idx, coeff in selected)))
    print(f"\n{name} certificate:")
    print(f"  rows used: {len(selected)}")
    print(f"  split-word terms before cancellation: {total_terms}")
    print("  labels and coefficients:")
    for idx, coeff in selected:
        print(f"    {coeff:+d} * {system.row_labels[idx]}")
    print(f"  polynomial: {poly}")
    return poly


def main_certificate() -> None:
    """
    Default rigorous path:
      - verifies Step-1 length-7 formulas against defining constraints,
      - derives exact length-15 distribution from Step 1 + forced u formula,
      - verifies Step-2 sparse certificates directly (LHS cancellation + RHS from dist15),
      - derives sparse Step-4 polynomial q(p,t), then proves univariate incompatibility.
    """
    p = sp.Symbol("p", real=True)
    t = sp.Symbol("t", real=True)

    print("Mode: rigorous certificate check (exact arithmetic)")

    # (1) Length-7 affine family from Step 1.
    dist7 = length7_distribution_closed_form(p, t)
    verify_length7_constraints(dist7, p)
    print("\nLength-7 cylinders in terms of (p,t), where t=P(1010101):")
    for w in sorted(dist7):
        print(" ", w, "=", sp.factor(dist7[w]))

    # Forced length-15 distribution in terms of (p,t).
    dist15 = dist15_in_terms_of_p_t(p, t)

    # (2) Compatibility polynomials from explicit sparse certificates.
    f = certificate_from_dist15(CERT_F, dist15, L=16, name="f")
    rpoly = certificate_from_dist15(CERT_R, dist15, L=20, name="r")

    f_expected = sp.factor(-3 * p**4 - 20 * p**3 + 6 * p**2 * t - 48 * p**2 + 30 * p * t + 45 * p - 3 * t**2 - 12 * t - 9)
    r_expected = sp.factor(-16 * p**4 + 12 * p**2 * t + 84 * p**2 - 60 * p * t - 60 * p + 9 * t**2 + 21 * t + 11)
    if sp.expand(f - f_expected) != 0:
        raise RuntimeError("unexpected: f-certificate polynomial mismatch")
    if sp.expand(rpoly - r_expected) != 0:
        raise RuntimeError("unexpected: r-certificate polynomial mismatch")

    g = sp.factor(sp.expand(3 * f + rpoly))
    print("\nCompatibility polynomials:")
    print("  f(p,t) =", sp.factor(f))
    print("  r(p,t) =", sp.factor(rpoly))
    print("  g(p,t) := 3*f + r =", g)

    # (3) Sparse Step-4 compatibility polynomial from short certificates.
    q = step4_sparse_polynomial_from_dist15(dist15, p, t)

    # Step 3: eliminate t from g=0 and substitute into f and q.
    den_t = 2 * p**2 + 2 * p - 1
    t_from_g = (25 * p**4 + 60 * p**3 + 60 * p**2 - 75 * p + 16) / (15 * (2 * p**2 + 2 * p - 1))
    g_sub = sp.together(sp.expand(g.subs({t: t_from_g})))
    g_num, _g_den = sp.fraction(g_sub)
    if sp.expand(g_num) != 0:
        raise RuntimeError("unexpected: t(p) does not satisfy g=0")
    print("\nUsing t(p) from g=0 gives:")
    print("  t =", t_from_g)

    f_sub = sp.together(f.subs({t: t_from_g}))
    num, den = sp.fraction(f_sub)
    num = sp.factor(num)
    den = sp.factor(den)
    print("\nSubstituting this t into f gives (up to a nonzero denominator):")
    print("  numerator factors as:")
    print(" ", num)
    print("  denominator:")
    print(" ", den)

    Apoly = 5 * p**4 - 355 * p**3 + 460 * p**2 - 200 * p + 29
    Bpoly = 5 * p**4 - 5 * p**3 - 5 * p**2 + 5 * p - 1
    assert sp.factor(num + Apoly * Bpoly) == 0 or sp.factor(num - (-Apoly * Bpoly)) == 0

    print("\nHence f=0 and g=0 imply:")
    print("  A(p) = 0 or B(p) = 0")
    print("  A(p) =", Apoly)
    print("  B(p) =", Bpoly)

    q_sub = sp.together(q.subs({t: t_from_g}))
    q_num, q_den = sp.fraction(q_sub)
    q_num = sp.factor(q_num)
    q_den = sp.factor(q_den)
    print("\nSubstituting this t into q gives (up to a nonzero denominator):")
    print("  numerator factors as:")
    print(" ", q_num)
    print("  denominator:")
    print(" ", q_den)

    P12 = sp.expand(
        500 * p**12
        - 306000 * p**11
        + 976500 * p**10
        + 6273000 * p**9
        - 11736300 * p**8
        - 1616400 * p**7
        + 16300800 * p**6
        - 13617000 * p**5
        + 4003260 * p**4
        + 377640 * p**3
        - 541710 * p**2
        + 129690 * p
        - 10579
    )
    if sp.expand(q_num - P12) != 0 and sp.expand(q_num + P12) != 0:
        raise RuntimeError("unexpected: q numerator did not match expected factorization")

    if sp.gcd(sp.expand(Apoly), sp.expand(den_t)) != 1:
        raise RuntimeError("unexpected: A shares factor with denominator term 2p^2+2p-1")
    if sp.gcd(sp.expand(Bpoly), sp.expand(den_t)) != 1:
        raise RuntimeError("unexpected: B shares factor with denominator term 2p^2+2p-1")
    if sp.gcd(sp.expand(Apoly), sp.expand(P12)) != 1:
        raise RuntimeError("unexpected: A and P12 have common factor")
    if sp.gcd(sp.expand(Bpoly), sp.expand(P12)) != 1:
        raise RuntimeError("unexpected: B and P12 have common factor")

    print("\nBut q=0 forces P12(p)=0, where")
    print("  P12(p) =", sp.factor(P12))
    print("and gcd(A,P12)=gcd(B,P12)=1, so A(p)B(p)=0 and P12(p)=0 are incompatible.")

    print("\nConclusion: no stationary 5-dependent MIS exists on Z.")


def main_full_audit() -> None:
    p = sp.Symbol("p", real=True)
    t = sp.Symbol("t", real=True)

    print("Mode: full exact audit (recomputes large linear systems)")

    # (1) Length-7 affine family.
    dist7 = length7_distribution_in_terms_of_p_t(p, t)
    print("Length-7 cylinders in terms of (p,t), where t=P(1010101):")
    for w in sorted(dist7):
        print(" ", w, "=", sp.factor(dist7[w]))

    # Forced length-15 distribution in terms of (p,t).
    dist15 = dist15_in_terms_of_p_t(p, t)

    # (2) Compatibility polynomials from sparse dual certificates on fixed systems.
    fixed16 = build_fixed_system_from_dist15(16, dist15)
    if fixed16.A.shape != (727, 151):
        raise RuntimeError(f"unexpected fixed length-16 system size: {fixed16.A.shape}")
    fixed20 = build_fixed_system_from_dist15(20, dist15)
    if fixed20.A.shape != (3002, 465):
        raise RuntimeError(f"unexpected fixed length-20 system size: {fixed20.A.shape}")
    print("\nFixed systems used for Step 2 certificates:")
    print(f"  length 16: rows={fixed16.A.shape[0]}, vars={fixed16.A.shape[1]}")
    print(f"  length 20: rows={fixed20.A.shape[0]}, vars={fixed20.A.shape[1]}")

    f = certificate_polynomial(fixed16, CERT_F, "f")
    rpoly = certificate_polynomial(fixed20, CERT_R, "r")

    f_expected = sp.factor(-3 * p**4 - 20 * p**3 + 6 * p**2 * t - 48 * p**2 + 30 * p * t + 45 * p - 3 * t**2 - 12 * t - 9)
    r_expected = sp.factor(-16 * p**4 + 12 * p**2 * t + 84 * p**2 - 60 * p * t - 60 * p + 9 * t**2 + 21 * t + 11)
    if sp.expand(f - f_expected) != 0:
        raise RuntimeError("unexpected: f-certificate polynomial mismatch")
    if sp.expand(rpoly - r_expected) != 0:
        raise RuntimeError("unexpected: r-certificate polynomial mismatch")

    g = sp.factor(sp.expand(3 * f + rpoly))
    print("\nCompatibility polynomials:")
    print("  f(p,t) =", sp.factor(f))
    print("  r(p,t) =", sp.factor(rpoly))
    print("  g(p,t) := 3*f + r =", g)

    # Sparse Step-4 polynomial from short certificates.
    q = step4_sparse_polynomial_from_dist15(dist15, p, t)

    # Solve g=0 for t (it is linear in t).
    den_t = 2 * p**2 + 2 * p - 1
    t_from_g = (25 * p**4 + 60 * p**3 + 60 * p**2 - 75 * p + 16) / (15 * den_t)
    print("\nSolving g(p,t)=0 for t gives:")
    print("  t =", t_from_g)

    # Substitute into f and factor the numerator: -(A(p)*B(p)).
    f_sub = sp.together(f.subs({t: t_from_g}))
    num, den = sp.fraction(f_sub)
    num = sp.factor(num)
    den = sp.factor(den)
    print("\nSubstituting this t into f gives (up to a nonzero denominator):")
    print("  numerator factors as:")
    print(" ", num)
    print("  denominator:")
    print(" ", den)

    Apoly = 5 * p**4 - 355 * p**3 + 460 * p**2 - 200 * p + 29
    Bpoly = 5 * p**4 - 5 * p**3 - 5 * p**2 + 5 * p - 1
    assert sp.factor(num + Apoly * Bpoly) == 0 or sp.factor(num - (-Apoly * Bpoly)) == 0

    print("\nHence f=0 and g=0 imply:")
    print("  A(p) = 0 or B(p) = 0")
    print("  A(p) =", Apoly)
    print("  B(p) =", Bpoly)

    q_sub = sp.together(q.subs({t: t_from_g}))
    q_num, q_den = sp.fraction(q_sub)
    q_num = sp.factor(q_num)
    q_den = sp.factor(q_den)
    print("\nSubstituting this t into q gives (up to a nonzero denominator):")
    print("  numerator factors as:")
    print(" ", q_num)
    print("  denominator:")
    print(" ", q_den)

    P12 = sp.expand(
        500 * p**12
        - 306000 * p**11
        + 976500 * p**10
        + 6273000 * p**9
        - 11736300 * p**8
        - 1616400 * p**7
        + 16300800 * p**6
        - 13617000 * p**5
        + 4003260 * p**4
        + 377640 * p**3
        - 541710 * p**2
        + 129690 * p
        - 10579
    )
    if sp.expand(q_num - P12) != 0 and sp.expand(q_num + P12) != 0:
        raise RuntimeError("unexpected: q numerator did not match expected factorization")

    if sp.gcd(sp.expand(Apoly), sp.expand(den_t)) != 1:
        raise RuntimeError("unexpected: A shares factor with denominator term 2p^2+2p-1")
    if sp.gcd(sp.expand(Bpoly), sp.expand(den_t)) != 1:
        raise RuntimeError("unexpected: B shares factor with denominator term 2p^2+2p-1")
    if sp.gcd(sp.expand(Apoly), sp.expand(P12)) != 1:
        raise RuntimeError("unexpected: A and P12 have common factor")
    if sp.gcd(sp.expand(Bpoly), sp.expand(P12)) != 1:
        raise RuntimeError("unexpected: B and P12 have common factor")

    print("\nBut q=0 forces P12(p)=0, where")
    print("  P12(p) =", sp.factor(P12))
    print("and gcd(A,P12)=gcd(B,P12)=1, so A(p)B(p)=0 and P12(p)=0 are incompatible.")

    print("\nConclusion: no stationary 5-dependent MIS exists on Z.")


if __name__ == "__main__":
    parser = argparse.ArgumentParser(
        description="Exact checks for impossibility of stationary 5-dependent MIS on Z."
    )
    parser.add_argument(
        "--full-audit",
        action="store_true",
        help="recompute from large linear systems (slow, exact)",
    )
    args = parser.parse_args()
    if args.full_audit:
        main_full_audit()
    else:
        main_certificate()
