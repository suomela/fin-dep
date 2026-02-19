import FiniteDependence.MIS.Basic

namespace FiniteDependence.MIS

/-!
No stationary 4-dependent State: algebraic core.

`PROOF_k_le_5.md` gives a short certificate-style argument producing two polynomial
constraints on `p = P(X₀=1)`:

  g(p) = p^3 - 9 p^2 + 6 p - 1 = 0
  h(p) = p * (p^3 + 40 p^2 - 36 p + 8) = 0

and then shows these cannot both hold (via an explicit Bézout combination).

This file formalizes that algebraic contradiction over `ℝ`.
-/

def g (p : ℝ) : ℝ := p ^ 3 - 9 * p ^ 2 + 6 * p - 1

def h1 (p : ℝ) : ℝ := p ^ 3 + 40 * p ^ 2 - 36 * p + 8

theorem bezout_g_h1 (p : ℝ) :
    (2793 * p ^ 2 + 112910 * p - 52441) * g p + (-2793 * p ^ 2 + 23947 * p - 6555) * h1 p = 1 := by
  -- This identity is produced by `sympy.gcdex` (see `scripts/prove_k4_impossible.py`).
  -- It is a short explicit certificate that `g` and `h1` are coprime over `ℚ[p]`.
  simp [g, h1]
  ring

theorem no_k4_algebra (p : ℝ) (hp_ne : p ≠ 0) (hg : g p = 0) (hh : p * h1 p = 0) : False := by
  have hh1 : h1 p = 0 := by
    have : p = 0 ∨ h1 p = 0 := by
      exact mul_eq_zero.mp hh
    exact this.resolve_left hp_ne
  have : (1 : ℝ) = 0 := by
    simpa [hg, hh1] using bezout_g_h1 p
  exact one_ne_zero this

/-!
Helper: extracting `g(p)=0` from the four length-10 certificate equations in
`PROOF_k_le_5.md` (Section 3.3).

We abstract the three length-10 cylinder probabilities as variables and show the
four equations force `g p = 0`.
-/

theorem g_of_four_equations (p P0010010010 P0010010100 P0101010100 : ℝ)
    (E1 : P0010010010 = (1 - 2 * p) ^ 2)
    (E2 : P0101010100 = -(2 * p - 1) * (3 * p - 1))
    (E3 : P0010010100 + P0101010100 = (1 - p) * (p ^ 2 / 2))
    (E4 : P0010010010 + P0010010100 = (p - 1) * (p ^ 2 + 4 * p - 2) / 2) :
    g p = 0 := by
  -- Solve for `P0010010100` from E3 and E4 and equate.
  have h3 : P0010010100 = (1 - p) * (p ^ 2 / 2) - P0101010100 := by
    exact eq_sub_of_add_eq E3
  have h4 : P0010010100 = (p - 1) * (p ^ 2 + 4 * p - 2) / 2 - P0010010010 := by
    have : P0010010100 + P0010010010 = (p - 1) * (p ^ 2 + 4 * p - 2) / 2 := by
      simpa [add_comm] using E4
    exact eq_sub_of_add_eq this

  have h34 :
      (1 - p) * (p ^ 2 / 2) - P0101010100 =
        (p - 1) * (p ^ 2 + 4 * p - 2) / 2 - P0010010010 := by
    calc
      (1 - p) * (p ^ 2 / 2) - P0101010100 = P0010010100 := by
        simpa using h3.symm
      _ = (p - 1) * (p ^ 2 + 4 * p - 2) / 2 - P0010010010 := by
        simpa using h4

  -- Substitute the explicit values of the cylinders from E1/E2.
  have h34' :
      (1 - p) * (p ^ 2 / 2) - (-(2 * p - 1) * (3 * p - 1)) =
        (p - 1) * (p ^ 2 + 4 * p - 2) / 2 - (1 - 2 * p) ^ 2 := by
    simpa [E1, E2] using h34

  have expr_zero :
      (1 - p) * (p ^ 2 / 2) - (-(2 * p - 1) * (3 * p - 1)) -
        ((p - 1) * (p ^ 2 + 4 * p - 2) / 2 - (1 - 2 * p) ^ 2) = 0 := by
    exact sub_eq_zero.mpr h34'

  have hring :
      (1 - p) * (p ^ 2 / 2) - (-(2 * p - 1) * (3 * p - 1)) -
        ((p - 1) * (p ^ 2 + 4 * p - 2) / 2 - (1 - 2 * p) ^ 2) = -g p := by
    simp [g]
    ring_nf

  have : -g p = 0 := hring.symm.trans expr_zero
  linarith

end FiniteDependence.MIS
