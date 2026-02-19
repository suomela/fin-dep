# Proof Verification Scripts

These scripts implement finite checks for `../main.tex`.

For MIS lower-bound scripts, correctness relies on exact symbolic arithmetic (SymPy). Floating-point
values are printed only for human intuition.

## How to Run

From `proof/` (recommended, with `uv`):

```sh
uv run python scripts/prove_weak2_threshold.py
uv run --with sympy python scripts/prove_k3_impossible.py
uv run --with sympy python scripts/prove_k4_impossible.py
uv run --with sympy python scripts/prove_k5_impossible.py
```

Full audit for `k=5` (slow):

```sh
uv run --with sympy python scripts/prove_k5_impossible.py --full-audit
```

Sparse-certificate discovery helper (optional):

```sh
uv run --with sympy --with scipy python scripts/find_k5_sparse_certificates.py
```

## What Each Script Checks

- `prove_weak2_threshold.py`:
  - checks that the ascent map from proper 3-colorings forbids `000` and `111`,
  - checks the explicit 4-block weak-2 -> MIS factor excludes local `11` and `000`.
- `prove_k3_impossible.py`:
  - derives forced length-5 cylinders from stationarity + 3-dependence,
  - derives a quadratic solvability condition at length 6,
  - exhibits an exact contradiction at length 9.
- `prove_k4_impossible.py`:
  - derives the length-10 solvability polynomial `g(p)=0`,
  - derives an independent length-14 polynomial identity `h(p)=0`,
  - proves incompatibility via `gcd(g,h)=1`.
- `prove_k5_impossible.py`:
  - default mode uses sparse exact certificates (`f`, `r`, and `q`) and elimination to derive
    incompatible univariate constraints,
  - `--full-audit` additionally rebuilds the large Step-2 fixed systems before applying the same
    certificates.
- `find_k5_sparse_certificates.py`:
  - searches sparse dual row combinations for Step-3 marginals,
  - converts them to exact rational certificates and prints support-size statistics.
