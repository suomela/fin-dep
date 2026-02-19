import FiniteDependence.MIS.Basic

namespace FiniteDependence.MIS

/-!
No stationary 3-dependent State: algebraic core.

In `PROOF_k_le_5.md`, existence of a stationary 3-dependent State implies there is a real
`p = P(X₀=1)` satisfying the two polynomial identities:

  (A)  3 p^2 - 6 p + 2 = 0
  (B)  (1-2p)(3p-1) = (1-p)(p^2-5p+2).

This file proves these two identities are incompatible over `ℝ`.
-/

theorem no_k3_algebra (p : ℝ)
    (hp : 3 * p ^ 2 - 6 * p + 2 = 0)
    (hstar : (1 - 2 * p) * (3 * p - 1) = (1 - p) * (p ^ 2 - 5 * p + 2)) :
    False := by
  -- Isolate `p^2` from (A).
  have hp' : 3 * p ^ 2 = 6 * p - 2 := by
    calc
      3 * p ^ 2 = (3 * p ^ 2 - 6 * p + 2) + (6 * p - 2) := by ring
      _ = 0 + (6 * p - 2) := by simpa [hp]
      _ = 6 * p - 2 := by ring
  have hp2 : p ^ 2 = 2 * p - (2 / 3 : ℝ) := by
    calc
      p ^ 2 = (3 * p ^ 2) / 3 := by ring
      _ = (6 * p - 2) / 3 := by simp [hp']
      _ = 2 * p - (2 / 3 : ℝ) := by ring

  -- Rearrange (B) to a single polynomial equation.
  have hdiff : (1 - 2 * p) * (3 * p - 1) - (1 - p) * (p ^ 2 - 5 * p + 2) = 0 := by
    simpa [hstar]
  have hpoly : p ^ 3 - 12 * p ^ 2 + 12 * p - 3 = 0 := by
    simpa
        [show
            (1 - 2 * p) * (3 * p - 1) - (1 - p) * (p ^ 2 - 5 * p + 2) =
              p ^ 3 - 12 * p ^ 2 + 12 * p - 3 by
          ring] using
      hdiff

  -- Compute `p^3` from `p^2`.
  have hp3 : p ^ 3 = (10 / 3 : ℝ) * p - (4 / 3 : ℝ) := by
    calc
      p ^ 3 = p * p ^ 2 := by ring
      _ = p * (2 * p - (2 / 3 : ℝ)) := by simp [hp2]
      _ = 2 * p ^ 2 - (2 / 3 : ℝ) * p := by ring
      _ = 2 * (2 * p - (2 / 3 : ℝ)) - (2 / 3 : ℝ) * p := by simp [hp2]
      _ = (10 / 3 : ℝ) * p - (4 / 3 : ℝ) := by ring

  -- Substitute to get a linear equation in `p`.
  have hlin' :
      (10 / 3 : ℝ) * p - (4 / 3 : ℝ) - 12 * (2 * p - (2 / 3 : ℝ)) + 12 * p - 3 = 0 := by
    simpa [hp2, hp3] using hpoly
  have hlin_frac : (-26 / 3 : ℝ) * p + (11 / 3 : ℝ) = 0 := by
    simpa
        [show
            (10 / 3 : ℝ) * p - (4 / 3 : ℝ) - 12 * (2 * p - (2 / 3 : ℝ)) + 12 * p - 3 =
              (-26 / 3 : ℝ) * p + (11 / 3 : ℝ) by
          ring] using
      hlin'
  have hlin : (26 : ℝ) * p - 11 = 0 := by
    -- Multiply by 3 to clear denominators, then normalize.
    have hmul : (3 : ℝ) * ((-26 / 3 : ℝ) * p + (11 / 3 : ℝ)) = 0 := by
      simpa using congrArg (fun x => (3 : ℝ) * x) hlin_frac
    have hmul' : (-26 : ℝ) * p + 11 = 0 := by
      -- `ring_nf` turns `hmul` into a clean linear form.
      have hmul'' := hmul
      ring_nf at hmul''
      linarith [hmul'']
    linarith [hmul']

  -- Conclude `p = 11/26`.
  have hp_val : p = (11 / 26 : ℝ) := by
    have hmul : (26 : ℝ) * p = 11 := by linarith [hlin]
    have hmul' : p * (26 : ℝ) = 11 := by simpa [mul_comm] using hmul
    have h26 : (26 : ℝ) ≠ 0 := by norm_num
    exact (eq_div_iff h26).2 hmul'

  -- But then (A) becomes a false numerical identity.
  have hEq : (-1 / 676 : ℝ) = 0 := by
    have hp0 : 3 * (11 / 26 : ℝ) ^ 2 - 6 * (11 / 26 : ℝ) + 2 = 0 := by
      simpa [hp_val] using hp
    have hnum :
        3 * (11 / 26 : ℝ) ^ 2 - 6 * (11 / 26 : ℝ) + 2 = (-1 / 676 : ℝ) := by
      norm_num
    exact by simpa [hnum] using hp0
  have hNe : (-1 / 676 : ℝ) ≠ 0 := by norm_num
  exact hNe hEq

end FiniteDependence.MIS
