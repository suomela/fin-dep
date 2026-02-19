"""
Proof script (exact arithmetic) that no stationary 3-dependent MIS exists on Z.

We model an MIS indicator process (X_i) on Z as a {0,1}-process with forbidden
words '11' (independence) and '000' (maximality).

Strategy:
1) Use stationarity + 3-dependence to solve for length-5 cylinder probabilities
   in terms of p := P(X_0=1).
2) Impose the additional 3-dependence constraints at length 6. The resulting
   overdetermined *linear* system is solvable iff p satisfies a quadratic,
   forcing p = 1 - 1/sqrt(3), and yields a unique length-6 distribution.
3) Extend uniquely to length 8 (again via linear extension systems).
4) Derive an explicit contradiction at length 9 from just two constraints:
   - a suffix-marginal constraint implies P(010100100) = P(10100100);
   - 3-dependence + the SFT constraints imply P(010100100) = (1-p) P(00100).
   The two RHS values differ at the forced p.

Run:
  uv run --with sympy python scripts/prove_k3_impossible.py
"""

from __future__ import annotations

import itertools
from dataclasses import dataclass

import sympy as sp


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


@dataclass(frozen=True)
class LinearSystem:
    A: sp.Matrix
    b: sp.Matrix
    words: list[str]


def build_extension_system(
    dist_prev: dict[str, sp.Expr], k: int, *, with_labels: bool = False
):
    L_prev = len(next(iter(dist_prev)))
    L = L_prev + 1

    W = sorted(allowed_words(L))
    vars = [sp.Symbol("P" + w) for w in W]
    var_map = {w: vars[i] for i, w in enumerate(W)}

    eqs: list[sp.Expr] = []
    labels: list[tuple[str, object]] = []

    eqs.append(sum(vars) - 1)
    labels.append(("norm", None))

    for u, val in dist_prev.items():
        eqs.append(sum(var_map[w] for w in W if w.startswith(u)) - val)
        labels.append(("pref", u))
        eqs.append(sum(var_map[w] for w in W if w.endswith(u)) - val)
        labels.append(("suf", u))

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
                    if w in var_map:
                        lhs += var_map[w]
                eqs.append(lhs - rhs)
                labels.append(("indep", (m, x, n, y)))

    eqs_s: list[sp.Expr] = []
    labels_s: list[tuple[str, object]] = []
    for e, lbl in zip(eqs, labels):
        e = sp.simplify(e)
        if e == 0:
            continue
        eqs_s.append(e)
        labels_s.append(lbl)

    A = sp.zeros(len(eqs_s), len(vars))
    b = sp.zeros(len(eqs_s), 1)
    for i, expr in enumerate(eqs_s):
        expr = sp.expand(expr)
        const = expr
        for j, v in enumerate(vars):
            coeff = expr.coeff(v)
            A[i, j] = sp.Integer(coeff)
            const = sp.simplify(const - coeff * v)
        b[i, 0] = -sp.simplify(const)

    system = LinearSystem(A=A, b=b, words=W)
    if with_labels:
        return system, labels_s
    return system


def solve_extension(dist_prev: dict[str, sp.Expr], k: int) -> dict[str, sp.Expr] | None:
    system = build_extension_system(dist_prev, k)
    sol = sp.linsolve((system.A, system.b))
    sols = list(sol)
    if len(sols) != 1:
        return None
    vec = sols[0]
    return {w: sp.simplify(vec[i]) for i, w in enumerate(system.words)}


def left_nullspace_certificate(A: sp.Matrix, b: sp.Matrix):
    """
    If A x = b is inconsistent, return an integer vector v with v^T A = 0
    and v^T b != 0. Otherwise return None.
    """
    N = A.T.nullspace()
    for v in N:
        c = sp.simplify((v.T * b)[0])
        if c == 0:
            continue
        denoms = [sp.denom(x) for x in v]
        scale = sp.ilcm(*denoms)
        # v is a column Matrix; iterate by index for robust scalar extraction.
        entries = [sp.Integer(v[i, 0] * scale) for i in range(v.rows)]
        g = sp.gcd_list(entries)
        entries = [e // g for e in entries]
        vint = sp.Matrix(entries)
        c2 = sp.simplify((vint.T * b)[0])
        if c2 != 0:
            return vint, c2
    return None


def length5_distribution_symbolic(p: sp.Symbol) -> dict[str, sp.Expr]:
    W5 = sorted(allowed_words(5))
    W4 = sorted(allowed_words(4))
    vars5 = [sp.Symbol("P" + w) for w in W5]
    var_map = {w: vars5[i] for i, w in enumerate(W5)}

    P1 = {"0": 1 - p, "1": p}

    eqs: list[sp.Expr] = []
    eqs.append(sum(vars5) - 1)

    # stationarity at length4
    for u in W4:
        eqs.append(
            sum(var_map[w] for w in W5 if w.startswith(u))
            - sum(var_map[w] for w in W5 if w.endswith(u))
        )

    # one-site marginal
    eqs.append(sum(var_map[w] for w in W5 if w[0] == "1") - p)

    # 3-dependence at distance 4: X0 ⟂ X4 (gap=3)
    for a in "01":
        for b in "01":
            lhs = sum(var_map[w] for w in W5 if w[0] == a and w[4] == b)
            rhs = sp.simplify(P1[a] * P1[b])
            eqs.append(lhs - rhs)

    eqs = [sp.simplify(e) for e in eqs if sp.simplify(e) != 0]
    sol = sp.linsolve(eqs, vars5)
    sols = list(sol)
    if len(sols) != 1:
        raise RuntimeError(f"unexpected: length-5 solution set has size {len(sols)}")
    vec = sols[0]
    return {w: sp.simplify(vec[i]) for i, w in enumerate(W5)}


def length6_solvability_polynomial(p: sp.Symbol, dist5: dict[str, sp.Expr]) -> sp.Expr:
    W6 = sorted(allowed_words(6))
    vars6 = [sp.Symbol("P" + w) for w in W6]
    var_index = {w: i for i, w in enumerate(W6)}

    P1 = {"0": 1 - p, "1": p}
    # Determined from MIS constraints + stationarity.
    P2 = {"00": 1 - 2 * p, "01": p, "10": p, "11": sp.Integer(0)}

    eqs: list[sp.Expr] = []
    # prefix/suffix length-5 marginals
    for u, rhs in dist5.items():
        eqs.append(sum(vars6[var_index[w]] for w in W6 if w.startswith(u)) - rhs)
        eqs.append(sum(vars6[var_index[w]] for w in W6 if w.endswith(u)) - rhs)

    # indep: X0 ⟂ (X4,X5)  (split 1 + 3 + 2)
    for x in ["0", "1"]:
        for y in ["00", "01", "10", "11"]:
            rhs = sp.simplify(P1[x] * P2[y])
            lhs = sum(vars6[var_index[w]] for w in W6 if w[0] == x and w[4:6] == y)
            eqs.append(lhs - rhs)

    # indep: (X0,X1) ⟂ X5  (split 2 + 3 + 1)
    for x in ["00", "01", "10", "11"]:
        for y in ["0", "1"]:
            rhs = sp.simplify(P2[x] * P1[y])
            lhs = sum(vars6[var_index[w]] for w in W6 if w[0:2] == x and w[5] == y)
            eqs.append(lhs - rhs)

    eqs = [sp.simplify(e) for e in eqs if sp.simplify(e) != 0]

    A = sp.zeros(len(eqs), len(vars6))
    b = sp.zeros(len(eqs), 1)
    for i, expr in enumerate(eqs):
        expr = sp.expand(expr)
        const = expr
        for j, v in enumerate(vars6):
            coeff = expr.coeff(v)
            A[i, j] = sp.Integer(coeff)
            const = sp.simplify(const - coeff * v)
        b[i, 0] = -sp.simplify(const)

    # Conditions for solvability come from the left nullspace of A.
    N = A.T.nullspace()
    conditions: list[sp.Expr] = []
    for v in N:
        c = sp.simplify((v.T * b)[0])
        if c != 0:
            num, den = sp.fraction(c)
            if sp.Poly(den, p).degree() != 0:
                raise RuntimeError("unexpected p-dependent denominator")
            conditions.append(sp.factor(num))
    if not conditions:
        return sp.Integer(0)

    g = conditions[0]
    for h in conditions[1:]:
        g = sp.gcd(g, h)
    return sp.factor(g)


def solve_length6_at_p(p_val: sp.Expr, dist5: dict[str, sp.Expr]) -> dict[str, sp.Expr]:
    p = sp.Symbol("p")
    p_subs = {p: p_val}
    dist5_eval = {w: sp.simplify(v.subs(p_subs)) for w, v in dist5.items()}

    W6 = sorted(allowed_words(6))
    vars6 = [sp.Symbol("P" + w) for w in W6]
    var_index = {w: i for i, w in enumerate(W6)}

    P1 = {"0": 1 - p_val, "1": p_val}
    P2 = {"00": 1 - 2 * p_val, "01": p_val, "10": p_val, "11": sp.Integer(0)}

    eqs: list[sp.Expr] = []
    for u, rhs in dist5_eval.items():
        eqs.append(sum(vars6[var_index[w]] for w in W6 if w.startswith(u)) - rhs)
        eqs.append(sum(vars6[var_index[w]] for w in W6 if w.endswith(u)) - rhs)

    for x in ["0", "1"]:
        for y in ["00", "01", "10", "11"]:
            rhs = sp.simplify(P1[x] * P2[y])
            lhs = sum(vars6[var_index[w]] for w in W6 if w[0] == x and w[4:6] == y)
            eqs.append(lhs - rhs)

    for x in ["00", "01", "10", "11"]:
        for y in ["0", "1"]:
            rhs = sp.simplify(P2[x] * P1[y])
            lhs = sum(vars6[var_index[w]] for w in W6 if w[0:2] == x and w[5] == y)
            eqs.append(lhs - rhs)

    eqs = [sp.simplify(e) for e in eqs if sp.simplify(e) != 0]
    sol = sp.linsolve(eqs, vars6)
    sols = list(sol)
    if len(sols) != 1:
        raise RuntimeError(f"unexpected: length-6 solution set has size {len(sols)}")
    vec = sols[0]
    return {w: sp.simplify(vec[i]) for i, w in enumerate(W6)}


def main() -> None:
    p = sp.Symbol("p")

    dist5 = length5_distribution_symbolic(p)
    print("Length-5 distribution (in terms of p):")
    for w in sorted(dist5):
        print(" ", w, "=", sp.factor(dist5[w]))

    g = length6_solvability_polynomial(p, dist5)
    print("\nLength-6 solvability gcd polynomial:", g)

    # Solve for p and pick the root in [1/3, 1/2].
    roots = [r for r in sp.solve(g, p) if r.is_real]
    p_candidates = []
    for r in roots:
        rv = float(sp.N(r))
        if 1 / 3 - 1e-9 <= rv <= 1 / 2 + 1e-9:
            p_candidates.append(r)
    if len(p_candidates) != 1:
        raise RuntimeError(f"expected 1 feasible root for p, got: {p_candidates}")
    p_star = sp.simplify(p_candidates[0])
    print("Forced p =", p_star, "≈", float(sp.N(p_star)))

    dist6 = solve_length6_at_p(p_star, dist5)
    print("\nLength-6 distribution at forced p:")
    for w in sorted(dist6):
        print(" ", w, "=", sp.simplify(dist6[w]))
    print(" sum =", sp.simplify(sum(dist6.values())))

    # Extend uniquely to length 8.
    dist7 = solve_extension(dist6, 3)
    dist8 = solve_extension(dist7, 3) if dist7 is not None else None
    if dist7 is None or dist8 is None:
        raise RuntimeError("unexpected: failed to extend to length 8")

    u8 = "10100100"
    if u8 not in dist8:
        raise RuntimeError(f"expected {u8} to be an allowed length-8 word")
    prob_u8 = sp.simplify(dist8[u8])

    # From length-5 distribution.
    w5 = "00100"
    prob_w5 = sp.simplify(dist5[w5].subs({p: p_star}))

    # The two constraints at length 9:
    #   (suffix)  P(010100100) = P(10100100)
    #   (indep)   P(010100100) = P(X0=0) P(00100) = (1-p) P(00100)
    lhs_word = "010100100"
    assert allowed_mis(lhs_word)
    assert lhs_word[1:] == u8

    # Check that 0 + g + 00100 is allowed for exactly one g (namely g=101),
    # so the independence equation really pins down P(lhs_word).
    allowed_mids = []
    for g_bits in itertools.product("01", repeat=3):
        mid = "".join(g_bits)
        cand = "0" + mid + w5
        if allowed_mis(cand):
            allowed_mids.append(mid)
    assert allowed_mids == ["101"]

    rhs_stationary = prob_u8
    rhs_indep = sp.simplify((1 - p_star) * prob_w5)
    diff = sp.simplify(rhs_stationary - rhs_indep)

    print("\nContradiction at length 9 from two equations:")
    print("  From suffix-marginal:     P(010100100) =", rhs_stationary)
    print("  From 3-dependence + SFT:  P(010100100) =", rhs_indep)
    print("  Difference =", diff, "≈", float(sp.N(diff)))

    if diff == 0:
        raise RuntimeError("unexpected: contradiction vanished")

    # Additionally, exhibit the 2-equation left-nullspace certificate for the full length-9 system.
    system9, labels9 = build_extension_system(dist8, 3, with_labels=True)
    cert = left_nullspace_certificate(system9.A, system9.b)
    if cert is None:
        raise RuntimeError("unexpected: no left-nullspace certificate for inconsistent system")
    v, c = cert
    nz = [i for i, x in enumerate(v) if x != 0]
    print("\nLinear-algebra certificate for inconsistency of full length-9 extension system:")
    print("  rank(A) =", system9.A.rank(), "rank([A|b]) =", system9.A.row_join(system9.b).rank())
    print("  v^T b =", c)
    print("  nonzero rows in v:", nz)
    for i in nz:
        print("   ", int(v[i]), "*", labels9[i])


if __name__ == "__main__":
    main()
