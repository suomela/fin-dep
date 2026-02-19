# Human-Readable Proof Companion (LaTeX + Exact Scripts)

This directory contains the human-readable companion to the Lean 4 formalization in the repository
root.

## Contents

- `main.tex`: LaTeX writeup of the headline thresholds (proper 4/3-colorings, weak 2-colorings,
  greedy proper 3-colorings, and MIS).
- `main.pdf`: compiled version of `main.tex`.
- `scripts/`: exact-audit Python scripts for the finite computations used in the writeup.
  In `main.tex`, the `k=3` and `k=4` MIS lower bounds are presented as pen-and-paper proofs; the
  `k=5` MIS lower bound remains computer-assisted.

## Build the PDF

From `proof/`:

```sh
latexmk -pdf main.tex
```

## Run the Verification Scripts

From `proof/` (recommended, with `uv`):

```sh
uv run python scripts/prove_weak2_threshold.py
uv run --with sympy python scripts/prove_k3_impossible.py
uv run --with sympy python scripts/prove_k4_impossible.py
uv run --with sympy python scripts/prove_k5_impossible.py
```

Deep audit (slow):

```sh
uv run --with sympy python scripts/prove_k5_impossible.py --full-audit
```

See `scripts/README.md` for script-level details, including the sparse-certificate discovery helper.

## Lean Cross-Reference (Repository Root)

- Public API:
  - `FiniteDependence/API/Definitions.lean`
  - `FiniteDependence/API/MainTheorems.lean`
- Weak-2 threshold (`k=3` exists, `k=2` impossible):
  - `FiniteDependence/WeakTwo/Threshold.lean`
- Greedy proper 3-coloring threshold (`k=6` exists, `k=5` impossible):
  - `FiniteDependence/Coloring/GreedyThree.lean`
    (`FiniteDependence.Coloring.exists_stationary_sixDependent_greedyThreeColoring`,
    `FiniteDependence.Coloring.not_exists_stationary_fiveDependent_greedyThreeColoring`)
- MIS upper bound (`k=6` exists):
  - `FiniteDependence/Coloring/MIS.lean`
    (`FiniteDependence.Coloring.exists_stationary_sixDependent_MIS`)
- MIS lower bound (`k=5` impossible):
  - `FiniteDependence/MIS/K5Bridge/NoK5.lean`
    (`FiniteDependence.MIS.K5Bridge.Model.NoK5.no_k5`)
  - `FiniteDependence/MIS/LowerBounds/K5/Bridge.lean`
    (`FiniteDependence.LowerBoundBridge.not_exists_stationary_fiveDependent_MIS`)
