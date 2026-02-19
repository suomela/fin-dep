"""
Proof script (exact arithmetic audit) that no stationary 4-dependent MIS exists on Z.

MIS indicator process on Z = {0,1}-process forbidding '11' and '000'.

Outline:
1) Let p := P(X0=1).
2) Use stationarity + 4-dependence constraints at length 7 to force the entire
   length-7 cylinder distribution as an explicit polynomial function of p.
3) Extend uniquely to length 9 (linear extension systems).
4) At length 10, solvability requires a cubic constraint g(p)=0:
      g(p) = p^3 - 9 p^2 + 6 p - 1.
5) Independently, 4-dependence implies two identities for the same length-14 word
   (because the SFT constraints allow only one middle word '1001'):

      P(00100 1001 00100) = P(00100)^2
      P(00 1001 00100100) = P(00) P(00100100)

   but the LHS is the same word 00100100100100, hence

      P(00100)^2 = P(00) P(00100100).

   From the forced length-7/8 distributions one gets
      P(00100)    = -(p^2 + 4p - 2)/2,
      P(00100100) = (2p - 1)^2,
      P(00)       = 1 - 2p,
   so this becomes a polynomial equation h(p)=0.

6) Show gcd(g,h)=1, so g(p)=0 and h(p)=0 cannot hold simultaneously. Contradiction.

The corresponding `k=4` section of `proof/main.tex` now gives a pen-and-paper
derivation; this script serves as an independent exact check.

Run:
  uv run --with sympy python scripts/prove_k4_impossible.py
"""

from __future__ import annotations

import itertools

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


def solve_length7_in_terms_of_p(p: sp.Symbol) -> dict[str, sp.Expr]:
    """
    Solve for length-7 cylinders using:
    - normalization,
    - stationarity at length 6,
    - 4-dependence constraints for splits (1,2) and (2,1) with gap 4.
    """
    L = 7
    W7 = sorted(allowed_words(L))
    W6 = sorted(allowed_words(L - 1))
    vars7 = [sp.Symbol("P" + w) for w in W7]
    var_map = {w: vars7[i] for i, w in enumerate(W7)}

    P1 = {"0": 1 - p, "1": p}
    P2 = {"00": 1 - 2 * p, "01": p, "10": p, "11": sp.Integer(0)}

    eqs: list[sp.Expr] = []
    eqs.append(sum(vars7) - 1)

    # stationarity on length 6: prefix marginal equals suffix marginal
    for u in W6:
        eqs.append(
            sum(var_map[w] for w in W7 if w.startswith(u))
            - sum(var_map[w] for w in W7 if w.endswith(u))
        )

    # gap-4 independence for splits (1,2)
    for x in ["0", "1"]:
        for y in ["00", "01", "10", "11"]:
            rhs = sp.simplify(P1[x] * P2[y])
            lhs = 0
            for mid in itertools.product("01", repeat=4):
                w = x + "".join(mid) + y
                if w in var_map:
                    lhs += var_map[w]
            eqs.append(lhs - rhs)

    # gap-4 independence for splits (2,1)
    for x in ["00", "01", "10", "11"]:
        for y in ["0", "1"]:
            rhs = sp.simplify(P2[x] * P1[y])
            lhs = 0
            for mid in itertools.product("01", repeat=4):
                w = x + "".join(mid) + y
                if w in var_map:
                    lhs += var_map[w]
            eqs.append(lhs - rhs)

    eqs = [sp.simplify(e) for e in eqs if sp.simplify(e) != 0]
    sol = sp.linsolve(eqs, vars7)
    sols = list(sol)
    if len(sols) != 1:
        raise RuntimeError(f"unexpected: length-7 solution set has size {len(sols)}")
    vec = sols[0]

    # Ensure no extra free symbols beyond p.
    free = set().union(*[v.free_symbols for v in vec])
    free.discard(p)
    for v in vars7:
        free.discard(v)
    if free:
        raise RuntimeError(f"unexpected extra free parameters in length-7 solution: {free}")

    return {w: sp.simplify(vec[i]) for i, w in enumerate(W7)}


def solve_next(dist_prev: dict[str, sp.Expr], k: int) -> dict[str, sp.Expr]:
    L_prev = len(next(iter(dist_prev)))
    L = L_prev + 1

    W = sorted(allowed_words(L))
    vars = [sp.Symbol("P" + w) for w in W]
    var_map = {w: vars[i] for i, w in enumerate(W)}

    eqs: list[sp.Expr] = []
    eqs.append(sum(vars) - 1)

    for u, val in dist_prev.items():
        eqs.append(sum(var_map[w] for w in W if w.startswith(u)) - val)
        eqs.append(sum(var_map[w] for w in W if w.endswith(u)) - val)

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

    eqs = [sp.simplify(e) for e in eqs if sp.simplify(e) != 0]
    sol = sp.linsolve(eqs, vars)
    sols = list(sol)
    if len(sols) != 1:
        raise RuntimeError(f"unexpected: length-{L} solution set has size {len(sols)}")
    vec = sols[0]
    return {w: sp.simplify(vec[i]) for i, w in enumerate(W)}


def build_system(dist_prev: dict[str, sp.Expr], k: int) -> tuple[sp.Matrix, sp.Matrix]:
    L_prev = len(next(iter(dist_prev)))
    L = L_prev + 1

    W = sorted(allowed_words(L))
    vars = [sp.Symbol("P" + w) for w in W]
    var_map = {w: vars[i] for i, w in enumerate(W)}

    eqs: list[sp.Expr] = []
    eqs.append(sum(vars) - 1)

    for u, val in dist_prev.items():
        eqs.append(sum(var_map[w] for w in W if w.startswith(u)) - val)
        eqs.append(sum(var_map[w] for w in W if w.endswith(u)) - val)

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

    eqs = [sp.simplify(e) for e in eqs if sp.simplify(e) != 0]

    A = sp.zeros(len(eqs), len(vars))
    b = sp.zeros(len(eqs), 1)
    for i, expr in enumerate(eqs):
        expr = sp.expand(expr)
        const = expr
        for j, v in enumerate(vars):
            coeff = expr.coeff(v)
            A[i, j] = sp.Integer(coeff)
            const = sp.simplify(const - coeff * v)
        b[i, 0] = -sp.simplify(const)
    return A, b


def main() -> None:
    p = sp.Symbol("p")

    dist7 = solve_length7_in_terms_of_p(p)
    dist8 = solve_next(dist7, k=4)
    dist9 = solve_next(dist8, k=4)

    # Length-10 solvability condition from left nullspace of A10.
    A10, b10 = build_system(dist9, k=4)
    if A10.rank() != A10.cols:
        raise RuntimeError("unexpected: A10 not full column rank")
    conditions = []
    for v in A10.T.nullspace():
        c = sp.simplify((v.T * b10)[0])
        if c == 0:
            continue
        num, den = sp.fraction(c)
        if sp.Poly(den, p).degree() != 0:
            raise RuntimeError("unexpected p-dependent denominator")
        conditions.append(sp.factor(sp.together(num)))
    if not conditions:
        raise RuntimeError("unexpected: no solvability conditions at length 10")
    g = conditions[0]
    for h in conditions[1:]:
        g = sp.gcd(g, h)
    g = sp.factor(g)

    print("Length-10 solvability gcd polynomial g(p) =", g)

    # Forced short marginals from dist7/dist8.
    P00100 = sp.simplify(marginal(dist7, 5, 0)["00100"])
    P00100100 = sp.simplify(dist8["00100100"])
    P00 = 1 - 2 * p

    print("Forced P(00100)    =", sp.factor(P00100))
    print("Forced P(00100100) =", sp.factor(P00100100))
    print("Forced P(00)       =", sp.factor(P00))

    # Combinatorial fact: the middle word is uniquely forced to be '1001' in both cases.
    mids_1 = [
        "".join(bits)
        for bits in itertools.product("01", repeat=4)
        if allowed_mis("00100" + "".join(bits) + "00100")
    ]
    mids_2 = [
        "".join(bits)
        for bits in itertools.product("01", repeat=4)
        if allowed_mis("00" + "".join(bits) + "00100100")
    ]
    if mids_1 != ["1001"] or mids_2 != ["1001"]:
        raise RuntimeError(f"unexpected allowed mids: {mids_1=}, {mids_2=}")
    print("Unique middle word for both length-14 constraints:", mids_1[0])

    # Therefore 4-dependence forces:
    #   P(00100100100100) = P(00100)^2 = P(00) P(00100100).
    h = sp.simplify(P00100**2 - P00 * P00100100)
    num, den = sp.fraction(sp.together(h))
    if sp.Poly(den, p).degree() != 0:
        raise RuntimeError("unexpected p-dependent denominator in h")
    h_poly = sp.factor(num)

    print("\nNecessary polynomial identity h(p)=0 from the two length-14 constraints:")
    print("  h(p) =", h_poly)

    print("\nBut any solution must also satisfy g(p)=0 (from length-10 solvability).")
    print("gcd(g,h) =", sp.factor(sp.gcd(g, h_poly)))

    if sp.gcd(g, h_poly) != 1:
        raise RuntimeError("unexpected: gcd(g,h) not 1")

    # Also show explicitly that for any root of g, h is nonzero.
    roots = [r for r in sp.nroots(g) if abs(sp.im(r)) < 1e-12]
    print("\nReal roots of g and the value of h at those roots:")
    for r in roots:
        rv = float(sp.re(r))
        hv = float(sp.N(h_poly.subs({p: sp.re(r)})))
        print("  p ≈", rv, "  h(p) ≈", hv)

    print("\nConclusion: no stationary 4-dependent MIS process exists on Z.")


if __name__ == "__main__":
    main()
