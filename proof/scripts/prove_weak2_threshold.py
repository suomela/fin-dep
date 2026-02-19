"""
Finite checks for the weak-2-coloring threshold discussion in `../main.tex`.

Weak 2-coloring SFT on Z: forbid `000` and `111`.
MIS SFT on Z: forbid `11` and `000`.

This script verifies two local claims used in the proof:

1) Existence side (k=3):
   If `C` is a proper 3-coloring and `Y_i = 1{C_i < C_{i+1}}`, then `Y` forbids `000` and `111`.
   (Checked on all proper length-4 color words.)

2) Reduction side (no k=2):
   For the explicit 4-block local rule
     M_i = 1  iff  X_i..X_{i+3} in {0010,0011,1010,1011,1100},
   every weak-2 source word maps to MIS-local constraints:
     - no `11` on output adjacent pairs (checked on source length 5),
     - no `000` on output triples (checked on source length 6).

No floating point and no external packages are used.

Run:
  uv run python scripts/prove_weak2_threshold.py
"""

from __future__ import annotations

import itertools


def words(alphabet: str, length: int) -> list[str]:
    return ["".join(bits) for bits in itertools.product(alphabet, repeat=length)]


def weak2_ok(word: str) -> bool:
    return "000" not in word and "111" not in word


def proper3_ok(word: tuple[int, ...]) -> bool:
    return all(word[i] != word[i + 1] for i in range(len(word) - 1))


def verify_ascent_from_3coloring() -> None:
    bad: list[tuple[tuple[int, ...], tuple[int, int, int]]] = []
    for c in itertools.product(range(3), repeat=4):
        if not proper3_ok(c):
            continue
        y = tuple(int(c[i] < c[i + 1]) for i in range(3))
        if y == (0, 0, 0) or y == (1, 1, 1):
            bad.append((c, y))
    if bad:
        raise RuntimeError(f"unexpected counterexamples in 3-color ascent check: {bad[:5]}")

    total = sum(1 for c in itertools.product(range(3), repeat=4) if proper3_ok(c))
    print(f"[ok] proper-3-color ascent check on length 4: {total} words, no 000/111 in Y")


ONES = {"0010", "0011", "1010", "1011", "1100"}


def mis_factor_bit(window4: str) -> str:
    return "1" if window4 in ONES else "0"


def map_by_rule(word: str) -> str:
    if len(word) < 4:
        raise ValueError("map_by_rule expects length >= 4")
    return "".join(mis_factor_bit(word[i : i + 4]) for i in range(len(word) - 3))


def verify_weak2_to_mis_local_checks() -> None:
    bad_11: list[tuple[str, str]] = []
    bad_000: list[tuple[str, str]] = []

    allowed5 = [w for w in words("01", 5) if weak2_ok(w)]
    allowed6 = [w for w in words("01", 6) if weak2_ok(w)]

    for w in allowed5:
        out = map_by_rule(w)  # length 2
        if out == "11":
            bad_11.append((w, out))

    for w in allowed6:
        out = map_by_rule(w)  # length 3
        if out == "000":
            bad_000.append((w, out))

    if bad_11:
        raise RuntimeError(f"unexpected source->output 11 violations: {bad_11[:5]}")
    if bad_000:
        raise RuntimeError(f"unexpected source->output 000 violations: {bad_000[:5]}")

    print(
        "[ok] weak2->MIS local checks: "
        f"{len(allowed5)} source words (length 5), {len(allowed6)} source words (length 6), "
        "no output 11 or 000 violations"
    )


def main() -> None:
    print("Verifying weak-2-coloring threshold local certificates...")
    verify_ascent_from_3coloring()
    verify_weak2_to_mis_local_checks()
    print("[done] all finite checks passed")


if __name__ == "__main__":
    main()

