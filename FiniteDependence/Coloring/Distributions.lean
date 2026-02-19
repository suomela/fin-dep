import FiniteDependence.Coloring.Prop11Four
import FiniteDependence.Coloring.Prop11Three
import Mathlib.Probability.ProbabilityMassFunction.Basic

/-!
# Cylinder probability weights `P4` and `P3`

This file defines the explicit cylinder probability weights from Holroyd–Liggett,
*Finitely dependent coloring* (arXiv:1403.2448v4), expressed using the recursively-defined
combinatorial function `Word.B`.

For `q = 4` the paper defines, for a word `x : [4]^n`,

`P4(x) = B(x) / ((n+1)! * 2^n)`.

For `q = 3` it defines

`P3(x) = 2 * B(x) / (n+2)!`.

We also prove the basic normalization and marginalization identities needed later to build the
two-sided process on `ℤ` and to derive finite dependence.
-/

open scoped BigOperators ENNReal

noncomputable section

namespace FiniteDependence.Coloring

namespace Word

/-! ## Total `B`-mass -/

/-- `Σ(q,n) = ∑_{x∈[q]^n} B(x)` (Corollary 12 in the paper). -/
def Sigma (q n : ℕ) : ℕ :=
  ∑ x : Word q n, B (q := q) x

lemma Sigma_zero (q : ℕ) : Sigma q 0 = 1 := by
  classical
  simp [Sigma, B]

/-- Recurrence for `Σ(q,n)` obtained by summing Proposition 10 over all words. -/
theorem Sigma_succ (q : ℕ) (hq : 2 ≤ q) (n : ℕ) :
    Sigma q (n + 1) = (n * (q - 2) + q) * Sigma q n := by
  classical
  -- Rewrite the sum over words of length `n+1` using `Fin.snocEquiv`.
  have hsum :
      (∑ w : Word q (n + 1), B (q := q) w)
        = ∑ p : Word q n × Fin q, B (q := q) (snoc p.1 p.2) := by
    -- `Fin.snocEquiv` gives `Fin q × Word q n ≃ Word q (n+1)`; compose with `prodComm` to get
    -- `Word q n × Fin q ≃ Word q (n+1)` mapping `(x,a) ↦ snoc x a`.
    let e₀ : Fin q × Word q n ≃ Word q (n + 1) :=
      Fin.snocEquiv (fun _ : Fin (n + 1) => Fin q)
    let e : Word q n × Fin q ≃ Word q (n + 1) :=
      (Equiv.prodComm (Word q n) (Fin q)).trans e₀
    have h :
        (fun p : Word q n × Fin q => B (q := q) (snoc p.1 p.2))
          = fun p => B (q := q) (e p) := by
      rfl
    -- Transport the sum along `e`.
    simpa [Sigma, e, e₀, h] using
      (Fintype.sum_equiv (e := e) (f := fun p : Word q n × Fin q => B (q := q) (snoc p.1 p.2))
        (g := fun w : Word q (n + 1) => B (q := q) w) (h := fun _ => rfl)).symm

  -- Expand the sum over the product as an iterated sum.
  have hprod :
      (∑ p : Word q n × Fin q, B (q := q) (snoc p.1 p.2))
        = ∑ x : Word q n, ∑ a : Fin q, B (q := q) (snoc x a) := by
    -- `Fintype.sum_prod_type` sums over the first component then the second.
    simp [Fintype.sum_prod_type]

  -- Now use Proposition 10 (`sum_B_snoc`) pointwise and factor out the constant.
  calc
    Sigma q (n + 1)
        = ∑ w : Word q (n + 1), B (q := q) w := by
            simp [Sigma]
    _ = ∑ x : Word q n, ∑ a : Fin q, B (q := q) (snoc x a) := by
            simpa [Sigma] using hsum.trans hprod
    _ = ∑ x : Word q n, (n * (q - 2) + q) * B (q := q) x := by
            refine Fintype.sum_congr (fun x => ∑ a : Fin q, B (q := q) (snoc x a))
              (fun x => (n * (q - 2) + q) * B (q := q) x) ?_
            intro x
            simpa using (sum_B_snoc (q := q) hq (x := x))
    _ = (n * (q - 2) + q) * ∑ x : Word q n, B (q := q) x := by
            -- Pull out the constant factor.
            simp [Finset.mul_sum]
    _ = (n * (q - 2) + q) * Sigma q n := by
            simp [Sigma]

/-! ## Closed forms for `q = 3,4` -/

/-- `Σ(4,n) = (n+1)! * 2^n`. -/
theorem Sigma_four (n : ℕ) : Sigma 4 n = Nat.factorial (n + 1) * 2 ^ n := by
  classical
  induction n with
  | zero =>
      simp [Sigma_zero]
  | succ n ih =>
      have hrec := Sigma_succ (q := 4) (hq := by decide) (n := n)
      have hfac : n * (4 - 2) + 4 = 2 * (n + 2) := by
        omega
      calc
        Sigma 4 (n + 1) = (n * (4 - 2) + 4) * Sigma 4 n := hrec
        _ = (2 * (n + 2)) * (Nat.factorial (n + 1) * 2 ^ n) := by
              simp [hfac, ih]
        _ = Nat.factorial (n + 2) * 2 ^ (n + 1) := by
              simp [Nat.factorial_succ, Nat.pow_succ]
              ac_rfl

/-- `2 * Σ(3,n) = (n+2)!`. This avoids the `/2` in Corollary 12. -/
theorem two_mul_Sigma_three (n : ℕ) : 2 * Sigma 3 n = Nat.factorial (n + 2) := by
  classical
  induction n with
  | zero =>
      simp [Sigma_zero]
  | succ n ih =>
      have hrec := Sigma_succ (q := 3) (hq := by decide) (n := n)
      -- `n * (3-2) + 3 = n + 3`.
      have hfac : n * (3 - 2) + 3 = n + 3 := by
        simp
      -- Multiply the recurrence by `2` and use the inductive hypothesis.
      calc
        2 * Sigma 3 (n + 1)
            = 2 * ((n * (3 - 2) + 3) * Sigma 3 n) := by
                simp [hrec]
        _ = (n + 3) * (2 * Sigma 3 n) := by
              rw [hfac]
              ac_rfl
        _ = (n + 3) * Nat.factorial (n + 2) := by
              simp [ih]
        _ = Nat.factorial (n + 3) := by
              simp [Nat.factorial_succ, Nat.add_assoc]

/-! ## Cylinder weights -/

/-- Denominator for `P4` on words of length `n`: `(n+1)! * 2^n`. -/
def denom4 (n : ℕ) : ℕ :=
  Nat.factorial (n + 1) * 2 ^ n

/-- Denominator for `P3` on words of length `n`: `(n+2)!`. -/
def denom3 (n : ℕ) : ℕ :=
  Nat.factorial (n + 2)

lemma denom4_succ (n : ℕ) : denom4 (n + 1) = (2 * (n + 2)) * denom4 n := by
  unfold denom4
  simp [Nat.factorial_succ, Nat.pow_succ]
  ac_rfl

lemma denom3_succ (n : ℕ) : denom3 (n + 1) = (n + 3) * denom3 n := by
  simp [denom3, Nat.factorial_succ, Nat.add_assoc]

/-- Cylinder weight for the 4-coloring (equation (8) in the paper). -/
def P4 (n : ℕ) (x : Word 4 n) : ℝ≥0∞ :=
  (B (q := 4) x : ℝ≥0∞) / (denom4 n)

/-- Cylinder weight for the 3-coloring (equation (11) in the paper, using `Σ(3,n) = (n+2)!/2`). -/
def P3 (n : ℕ) (x : Word 3 n) : ℝ≥0∞ :=
  (2 * B (q := 3) x : ℝ≥0∞) / (denom3 n)

lemma denom4_pos (n : ℕ) : 0 < denom4 n := by
  have h1 : 0 < Nat.factorial (n + 1) := Nat.factorial_pos (n + 1)
  have h2 : 0 < 2 ^ n := Nat.pow_pos (by decide : 0 < (2 : ℕ))
  simpa [denom4, Nat.mul_pos] using Nat.mul_pos h1 h2

lemma denom3_pos (n : ℕ) : 0 < denom3 n := by
  simpa [denom3] using Nat.factorial_pos (n + 2)

lemma denom4_ne_zero (n : ℕ) : (denom4 n : ℝ≥0∞) ≠ 0 := by
  exact_mod_cast (Nat.ne_of_gt (denom4_pos n))

lemma denom3_ne_zero (n : ℕ) : (denom3 n : ℝ≥0∞) ≠ 0 := by
  exact_mod_cast (Nat.ne_of_gt (denom3_pos n))

lemma denom4_ne_top (n : ℕ) : (denom4 n : ℝ≥0∞) ≠ ⊤ := by
  -- `denom4 n` is a product of natural numbers, hence finite in `ℝ≥0∞`.
  -- First expand the casted product using `Nat.cast_mul`.
  simp [denom4, Nat.cast_mul, ENNReal.mul_ne_top]

lemma denom3_ne_top (n : ℕ) : (denom3 n : ℝ≥0∞) ≠ ⊤ := by
  simp [denom3]

/-! ## Normalization -/

theorem sum_P4 (n : ℕ) : (∑ x : Word 4 n, P4 n x) = 1 := by
  classical
  -- Turn the sum of quotients into a product with an inverse.
  have :
      (∑ x : Word 4 n, P4 n x)
        = (∑ x : Word 4 n, (B (q := 4) x : ℝ≥0∞)) * (denom4 n : ℝ≥0∞)⁻¹ := by
    simp [P4, div_eq_mul_inv, Finset.sum_mul]
  -- Use `Σ(4,n) = denom4 n`.
  have hSigma : (∑ x : Word 4 n, (B (q := 4) x : ℝ≥0∞)) = (denom4 n : ℝ≥0∞) := by
    -- Cast `Sigma_four` to `ℝ≥0∞`.
    have := congrArg (fun t : ℕ => (t : ℝ≥0∞)) (Sigma_four n)
    simpa [Sigma, denom4] using this
  -- Finish by cancelling.
  calc
    (∑ x : Word 4 n, P4 n x)
        = (denom4 n : ℝ≥0∞) * (denom4 n : ℝ≥0∞)⁻¹ := by
              simp [this, hSigma]
    _ = 1 := ENNReal.mul_inv_cancel (denom4_ne_zero n) (denom4_ne_top n)

theorem sum_P3 (n : ℕ) : (∑ x : Word 3 n, P3 n x) = 1 := by
  classical
  have :
      (∑ x : Word 3 n, P3 n x)
        = (2 * (∑ x : Word 3 n, (B (q := 3) x : ℝ≥0∞))) * (denom3 n : ℝ≥0∞)⁻¹ := by
    -- Pull out the constant factors `2` and `denom3`.
    simp [P3, div_eq_mul_inv, Finset.sum_mul, Finset.mul_sum]
  have hSigma : (2 * Sigma 3 n : ℝ≥0∞) = denom3 n := by
    have := congrArg (fun t : ℕ => (t : ℝ≥0∞)) (two_mul_Sigma_three n)
    simpa [denom3] using this
  have hsumB : (∑ x : Word 3 n, (B (q := 3) x : ℝ≥0∞)) = (Sigma 3 n : ℝ≥0∞) := by
    simp [Sigma]
  calc
    (∑ x : Word 3 n, P3 n x)
        = (2 * (Sigma 3 n : ℝ≥0∞)) * (denom3 n : ℝ≥0∞)⁻¹ := by
              simp [this, hsumB]
    _ = (denom3 n : ℝ≥0∞) * (denom3 n : ℝ≥0∞)⁻¹ := by
          simp [hSigma]
    _ = 1 := ENNReal.mul_inv_cancel (denom3_ne_zero n) (denom3_ne_top n)

/-! ## One-step marginals -/

theorem sum_P4_snoc (n : ℕ) (x : Word 4 n) :
    (∑ a : Fin 4, P4 (n + 1) (snoc x a)) = P4 n x := by
  classical
  have hB : (∑ a : Fin 4, B (q := 4) (snoc x a)) = (2 * (n + 2)) * B (q := 4) x := by
    -- Proposition 10 (right-end version), specialized to `q = 4`.
    have h := sum_B_snoc (q := 4) (hq := by decide) (x := x)
    -- `n * (4 - 2) + 4 = 2 * (n + 2)`.
    have hfac : n * (4 - 2) + 4 = 2 * (n + 2) := by
      omega
    simpa [hfac, Nat.mul_assoc, Nat.mul_left_comm, Nat.mul_comm] using h
  have hB' :
      (∑ a : Fin 4, (B (q := 4) (snoc x a) : ℝ≥0∞))
        = ((2 * (n + 2)) * B (q := 4) x : ℝ≥0∞) := by
    exact_mod_cast hB
  -- Turn the LHS sum into a single division by the constant denominator.
  have hsum :
      (∑ a : Fin 4, P4 (n + 1) (snoc x a))
        = (∑ a : Fin 4, (B (q := 4) (snoc x a) : ℝ≥0∞)) / (denom4 (n + 1)) := by
    simp [P4, div_eq_mul_inv, Finset.sum_mul]
  -- Cancel the common factor `2 * (n+2)` in numerator/denominator.
  let cNat : ℕ := 2 * (n + 2)
  let c : ℝ≥0∞ := (cNat : ℝ≥0∞)
  have hc0 : c ≠ 0 := by
    have hcNat_pos : 0 < cNat := Nat.mul_pos (by decide : 0 < (2 : ℕ)) (Nat.succ_pos _)
    have : (cNat : ℝ≥0∞) ≠ 0 := by
      exact_mod_cast (Nat.ne_of_gt hcNat_pos)
    simpa [c] using this
  have hct : c ≠ ⊤ := by simp [c]
  have hden : (denom4 (n + 1) : ℝ≥0∞) = c * (denom4 n : ℝ≥0∞) := by
    -- `denom4 (n+1) = cNat * denom4 n`.
    simpa [cNat, c, Nat.cast_mul, mul_assoc] using congrArg (fun t : ℕ => (t : ℝ≥0∞)) (denom4_succ n)
  calc
    (∑ a : Fin 4, P4 (n + 1) (snoc x a))
        = ((2 * (n + 2) * B (q := 4) x : ℝ≥0∞) / (denom4 (n + 1))) := by
              simp [hsum, hB']
    _ = (c * (B (q := 4) x : ℝ≥0∞)) / (c * (denom4 n : ℝ≥0∞)) := by
          simp [cNat, c, hden, Nat.cast_mul, mul_assoc]
    _ = (B (q := 4) x : ℝ≥0∞) / (denom4 n : ℝ≥0∞) := by
          simpa [div_eq_mul_inv] using (ENNReal.mul_div_mul_left (a := (B (q := 4) x : ℝ≥0∞))
            (b := (denom4 n : ℝ≥0∞)) (c := c) hc0 hct)
    _ = P4 n x := by simp [P4]

theorem sum_P4_cons (n : ℕ) (x : Word 4 n) :
    (∑ a : Fin 4, P4 (n + 1) (cons a x)) = P4 n x := by
  classical
  have hB : (∑ a : Fin 4, B (q := 4) (cons a x)) = (2 * (n + 2)) * B (q := 4) x := by
    have h := sum_B_cons (q := 4) (by decide : 2 ≤ (4 : ℕ)) (x := x)
    have hfac : n * (4 - 2) + 4 = 2 * (n + 2) := by
      omega
    simpa [hfac, Nat.mul_assoc, Nat.mul_left_comm, Nat.mul_comm] using h
  have hB' :
      (∑ a : Fin 4, (B (q := 4) (cons a x) : ℝ≥0∞))
        = ((2 * (n + 2)) * B (q := 4) x : ℝ≥0∞) := by
    exact_mod_cast hB
  have hsum :
      (∑ a : Fin 4, P4 (n + 1) (cons a x))
        = (∑ a : Fin 4, (B (q := 4) (cons a x) : ℝ≥0∞)) / (denom4 (n + 1)) := by
    simp [P4, div_eq_mul_inv, Finset.sum_mul]
  let cNat : ℕ := 2 * (n + 2)
  let c : ℝ≥0∞ := (cNat : ℝ≥0∞)
  have hc0 : c ≠ 0 := by
    have hcNat_pos : 0 < cNat := Nat.mul_pos (by decide : 0 < (2 : ℕ)) (Nat.succ_pos _)
    have : (cNat : ℝ≥0∞) ≠ 0 := by
      exact_mod_cast (Nat.ne_of_gt hcNat_pos)
    simpa [c] using this
  have hct : c ≠ ⊤ := by simp [c]
  have hden : (denom4 (n + 1) : ℝ≥0∞) = c * (denom4 n : ℝ≥0∞) := by
    simpa [cNat, c, Nat.cast_mul, mul_assoc] using congrArg (fun t : ℕ => (t : ℝ≥0∞)) (denom4_succ n)
  calc
    (∑ a : Fin 4, P4 (n + 1) (cons a x))
        = ((2 * (n + 2) * B (q := 4) x : ℝ≥0∞) / (denom4 (n + 1))) := by
              simp [hsum, hB']
    _ = (c * (B (q := 4) x : ℝ≥0∞)) / (c * (denom4 n : ℝ≥0∞)) := by
          simp [cNat, c, hden, Nat.cast_mul, mul_assoc]
    _ = (B (q := 4) x : ℝ≥0∞) / (denom4 n : ℝ≥0∞) := by
          simpa [div_eq_mul_inv] using (ENNReal.mul_div_mul_left (a := (B (q := 4) x : ℝ≥0∞))
            (b := (denom4 n : ℝ≥0∞)) (c := c) hc0 hct)
    _ = P4 n x := by simp [P4]

theorem sum_P3_snoc (n : ℕ) (x : Word 3 n) :
    (∑ a : Fin 3, P3 (n + 1) (snoc x a)) = P3 n x := by
  classical
  have hB : (∑ a : Fin 3, B (q := 3) (snoc x a)) = (n + 3) * B (q := 3) x := by
    have h := sum_B_snoc (q := 3) (hq := by decide) (x := x)
    have hfac : n * (3 - 2) + 3 = n + 3 := by
      simp
    simpa [hfac, Nat.mul_assoc, Nat.mul_left_comm, Nat.mul_comm] using h
  have hB' :
      (∑ a : Fin 3, (B (q := 3) (snoc x a) : ℝ≥0∞))
        = ((n + 3) * B (q := 3) x : ℝ≥0∞) := by
    exact_mod_cast hB
  have hsum :
      (∑ a : Fin 3, P3 (n + 1) (snoc x a))
        = (2 * (∑ a : Fin 3, (B (q := 3) (snoc x a) : ℝ≥0∞))) / (denom3 (n + 1)) := by
    simp [P3, div_eq_mul_inv, Finset.sum_mul, Finset.mul_sum]
  let cNat : ℕ := n + 3
  let c : ℝ≥0∞ := (cNat : ℝ≥0∞)
  have hc0 : c ≠ 0 := by
    have : 0 < cNat := Nat.succ_pos _
    have : (cNat : ℝ≥0∞) ≠ 0 := by
      exact_mod_cast (Nat.ne_of_gt this)
    simpa [c] using this
  have hct : c ≠ ⊤ := by simp [c]
  have hden : (denom3 (n + 1) : ℝ≥0∞) = c * (denom3 n : ℝ≥0∞) := by
    simpa [cNat, c, Nat.cast_mul, mul_assoc] using congrArg (fun t : ℕ => (t : ℝ≥0∞)) (denom3_succ n)
  calc
    (∑ a : Fin 3, P3 (n + 1) (snoc x a))
        = (2 * ((n + 3) * B (q := 3) x : ℝ≥0∞)) / (denom3 (n + 1)) := by
              simp [hsum, hB']
    _ = (c * ((2 * B (q := 3) x : ℝ≥0∞))) / (c * (denom3 n : ℝ≥0∞)) := by
          have hnum :
              (2 * ((n + 3) * B (q := 3) x : ℝ≥0∞))
                = c * (2 * B (q := 3) x : ℝ≥0∞) := by
            simp [cNat, c]
            ac_rfl
          simp [hden, hnum]
    _ = ((2 * B (q := 3) x : ℝ≥0∞)) / (denom3 n : ℝ≥0∞) := by
          simpa [div_eq_mul_inv] using (ENNReal.mul_div_mul_left (a := (2 * B (q := 3) x : ℝ≥0∞))
            (b := (denom3 n : ℝ≥0∞)) (c := c) hc0 hct)
    _ = P3 n x := by simp [P3]

theorem sum_P3_cons (n : ℕ) (x : Word 3 n) :
    (∑ a : Fin 3, P3 (n + 1) (cons a x)) = P3 n x := by
  classical
  have hB : (∑ a : Fin 3, B (q := 3) (cons a x)) = (n + 3) * B (q := 3) x := by
    have h := sum_B_cons (q := 3) (by decide : 2 ≤ (3 : ℕ)) (x := x)
    have hfac : n * (3 - 2) + 3 = n + 3 := by
      simp
    simpa [hfac, Nat.mul_assoc, Nat.mul_left_comm, Nat.mul_comm] using h
  have hB' :
      (∑ a : Fin 3, (B (q := 3) (cons a x) : ℝ≥0∞))
        = ((n + 3) * B (q := 3) x : ℝ≥0∞) := by
    exact_mod_cast hB
  have hsum :
      (∑ a : Fin 3, P3 (n + 1) (cons a x))
        = (2 * (∑ a : Fin 3, (B (q := 3) (cons a x) : ℝ≥0∞))) / (denom3 (n + 1)) := by
    simp [P3, div_eq_mul_inv, Finset.sum_mul, Finset.mul_sum]
  let cNat : ℕ := n + 3
  let c : ℝ≥0∞ := (cNat : ℝ≥0∞)
  have hc0 : c ≠ 0 := by
    have : 0 < cNat := Nat.succ_pos _
    have : (cNat : ℝ≥0∞) ≠ 0 := by
      exact_mod_cast (Nat.ne_of_gt this)
    simpa [c] using this
  have hct : c ≠ ⊤ := by simp [c]
  have hden : (denom3 (n + 1) : ℝ≥0∞) = c * (denom3 n : ℝ≥0∞) := by
    simpa [cNat, c, Nat.cast_mul, mul_assoc] using congrArg (fun t : ℕ => (t : ℝ≥0∞)) (denom3_succ n)
  calc
    (∑ a : Fin 3, P3 (n + 1) (cons a x))
        = (2 * ((n + 3) * B (q := 3) x : ℝ≥0∞)) / (denom3 (n + 1)) := by
              simp [hsum, hB']
    _ = (c * ((2 * B (q := 3) x : ℝ≥0∞))) / (c * (denom3 n : ℝ≥0∞)) := by
          have hnum :
              (2 * ((n + 3) * B (q := 3) x : ℝ≥0∞))
                = c * (2 * B (q := 3) x : ℝ≥0∞) := by
            simp [cNat, c]
            ac_rfl
          simp [hden, hnum]
    _ = ((2 * B (q := 3) x : ℝ≥0∞)) / (denom3 n : ℝ≥0∞) := by
          simpa [div_eq_mul_inv] using (ENNReal.mul_div_mul_left (a := (2 * B (q := 3) x : ℝ≥0∞))
            (b := (denom3 n : ℝ≥0∞)) (c := c) hc0 hct)
    _ = P3 n x := by simp [P3]

/-! ## `PMF` versions -/

/-- `P4` as a probability mass function on words of length `n`. -/
def pmf4 (n : ℕ) : PMF (Word 4 n) :=
  ⟨P4 n, by
    -- For a finite type, `HasSum f 1` follows from `∑ f = 1`.
    simpa [sum_P4 n] using (hasSum_fintype (P4 n))⟩

/-- `P3` as a probability mass function on words of length `n`. -/
def pmf3 (n : ℕ) : PMF (Word 3 n) :=
  ⟨P3 n, by
    simpa [sum_P3 n] using (hasSum_fintype (P3 n))⟩

/-! ## 1-dependence factorization identity for `q = 4` -/

private lemma denom4_factorization (m n : ℕ) :
    2 * Nat.choose (m + n + 2) (m + 1) * denom4 m * denom4 n = denom4 (m + 1 + n) := by
  -- Use `choose_mul_factorial_mul_factorial`.
  have hchoose :
      Nat.choose (m + n + 2) (m + 1) * Nat.factorial (m + 1) * Nat.factorial (n + 1)
        = Nat.factorial (m + n + 2) := by
    have hle : m + 1 ≤ m + n + 2 := by omega
    have hsub : m + n + 2 - (m + 1) = n + 1 := by omega
    simpa [hsub, Nat.mul_assoc] using
      (Nat.choose_mul_factorial_mul_factorial (n := m + n + 2) (k := m + 1) hle)

  -- A small power-of-two simplification.
  have hpow : 2 * (2 ^ m * 2 ^ n) = 2 ^ (m + n + 1) := by
    calc
      2 * (2 ^ m * 2 ^ n) = (2 ^ m * 2 ^ n) * 2 := by ac_rfl
      _ = 2 ^ (m + n) * 2 := by simp [Nat.pow_add, Nat.mul_assoc]
      _ = 2 ^ (m + n + 1) := by
            -- `2 ^ ((m+n)+1) = 2^(m+n) * 2`.
            simpa using (Nat.pow_succ 2 (m + n)).symm

  -- Now expand `denom4` and compute.
  unfold denom4
  -- `denom4 (m+1+n)` simplifies to `(m+n+2)! * 2^(m+n+1)`.
  have hmain :
      2 * Nat.choose (m + n + 2) (m + 1) * ((m + 1).factorial * 2 ^ m) * ((n + 1).factorial * 2 ^ n)
        = (m + n + 2).factorial * 2 ^ (m + n + 1) := by
      calc
        2 * Nat.choose (m + n + 2) (m + 1) * ((m + 1).factorial * 2 ^ m) * ((n + 1).factorial * 2 ^ n)
            = (Nat.choose (m + n + 2) (m + 1) * (m + 1).factorial * (n + 1).factorial)
                * (2 * (2 ^ m * 2 ^ n)) := by ac_rfl
        _ = (m + n + 2).factorial * (2 * (2 ^ m * 2 ^ n)) := by simp [hchoose]
        _ = (m + n + 2).factorial * 2 ^ (m + n + 1) := by simp [hpow]
  -- Rewrite the goal using associativity/commutativity of addition.
  simpa [Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using hmain

/-- Equation (10) in the paper, phrased for the normalized weights `P4`. -/
theorem sum_P4_insert1 (m n : ℕ) (x : Word 4 m) (y : Word 4 n) :
    (∑ a : Fin 4, P4 (m + 1 + n) (insert1 (q := 4) (m := m) (n := n) x a y))
      = P4 m x * P4 n y := by
  classical
  -- Start from Proposition 11 on `B`.
  have hB := sum_B_insert1_four (x := x) (y := y)
  -- Rewrite both sides in `ℝ≥0∞` and simplify denominators.
  -- First, convert the LHS to a single factor times `∑ B(...)`.
  have hL :
      (∑ a : Fin 4, P4 (m + 1 + n) (insert1 (q := 4) (m := m) (n := n) x a y))
        = (∑ a : Fin 4, (B (q := 4) (insert1 (q := 4) (m := m) (n := n) x a y) : ℝ≥0∞))
            * (denom4 (m + 1 + n) : ℝ≥0∞)⁻¹ := by
    simp [P4, div_eq_mul_inv, Finset.sum_mul]
  -- Cast the `Nat` identity `hB` to `ℝ≥0∞`.
  have hB' :
      (∑ a : Fin 4, (B (q := 4) (insert1 (q := 4) (m := m) (n := n) x a y) : ℝ≥0∞))
        = (2 * Nat.choose (m + n + 2) (m + 1) * B (q := 4) x * B (q := 4) y : ℝ≥0∞) := by
    -- `Nat.cast_sum` turns a nat sum into an `ℝ≥0∞` sum.
    exact_mod_cast hB
  -- RHS: expand `P4` and use the denominator factorization lemma.
  -- Combine `hL` and `hB'` to rewrite the LHS, then reduce to cancellation of the common factor
  -- `2 * choose(...)`.
  have hden : (denom4 (m + 1 + n) : ℝ≥0∞)
      = (2 * Nat.choose (m + n + 2) (m + 1) * denom4 m * denom4 n : ℝ≥0∞) := by
    exact_mod_cast (denom4_factorization m n).symm
  -- Reduce to a calculation in `ℝ≥0∞` using `a * a⁻¹ = 1` for the common normalizing factor.
  let aNat : ℕ := 2 * Nat.choose (m + n + 2) (m + 1)
  let a : ℝ≥0∞ := (aNat : ℝ≥0∞)
  let b : ℝ≥0∞ := (denom4 m : ℝ≥0∞)
  let c : ℝ≥0∞ := (denom4 n : ℝ≥0∞)
  let u : ℝ≥0∞ := (B (q := 4) x : ℝ≥0∞)
  let v : ℝ≥0∞ := (B (q := 4) y : ℝ≥0∞)

  have ha_pos : 0 < aNat := by
    have hle : m + 1 ≤ m + n + 2 := by omega
    exact Nat.mul_pos (by decide : 0 < (2 : ℕ)) (Nat.choose_pos hle)
  have ha0 : a ≠ 0 := by
    -- `a` is a positive natural number.
    have : (aNat : ℝ≥0∞) ≠ 0 := by
      exact_mod_cast (Nat.ne_of_gt ha_pos)
    simpa [a] using this
  have hat : a ≠ ⊤ := by
    -- `a` is a product of naturals, hence finite.
    simp [a]
  have hbtop : b ≠ ⊤ := denom4_ne_top m
  have hctop : c ≠ ⊤ := denom4_ne_top n
  have hb0 : b ≠ 0 := denom4_ne_zero m
  have hc0 : c ≠ 0 := denom4_ne_zero n
  have habc : (a * (b * c))⁻¹ = a⁻¹ * (b * c)⁻¹ :=
    ENNReal.mul_inv (a := a) (b := b * c) (Or.inr (ENNReal.mul_ne_top hbtop hctop)) (Or.inl hat)
  have hbc : (b * c)⁻¹ = b⁻¹ * c⁻¹ :=
    ENNReal.mul_inv (a := b) (b := c) (Or.inr hctop) (Or.inl hbtop)

  -- Now compute both sides.
  calc
    (∑ a' : Fin 4, P4 (m + 1 + n) (insert1 (q := 4) (m := m) (n := n) x a' y))
        = (a * u * v) * (a * (b * c))⁻¹ := by
            -- Rewrite the LHS using `hL`, `hB'`, and `hden`.
            -- We keep products grouped as `a * u * v` and `a * (b*c)` to simplify inverses.
            have hden' : (denom4 (m + 1 + n) : ℝ≥0∞) = a * (b * c) := by
              -- `hden` gives `denom4 = a * b * c`; reassociate.
              -- First rewrite `2 * choose` as the cast of `aNat`.
              simpa [a, b, c, aNat, Nat.cast_mul, mul_assoc] using hden
            -- Use `hL` and `hB'` explicitly, then substitute the denominator.
            calc
              (∑ a' : Fin 4, P4 (m + 1 + n) (insert1 (q := 4) (m := m) (n := n) x a' y))
                  = (2 * Nat.choose (m + n + 2) (m + 1) * B (q := 4) x * B (q := 4) y : ℝ≥0∞)
                      * (denom4 (m + 1 + n) : ℝ≥0∞)⁻¹ := by
                        -- `hL` rewrites the sum, `hB'` rewrites the `B`-sum.
                        simp [hL, hB']
              _ = (a * u * v) * (a * (b * c))⁻¹ := by
                    -- Rewrite the numerator (a cast of a natural product) as a product of casts.
                    have hnum :
                        (2 * Nat.choose (m + n + 2) (m + 1) * B (q := 4) x * B (q := 4) y : ℝ≥0∞)
                          = a * u * v := by
                      -- `aNat = 2 * choose(...)` by definition.
                      simp [aNat, a, u, v, Nat.cast_mul, mul_assoc]
                    -- Substitute both `hnum` and `hden'` using rewriting.
                    -- We use `rw` (rather than `simp`) to avoid rewriting casts before applying `hnum`.
                    rw [hden', hnum]
    _ = (a * u * v) * (a⁻¹ * (b * c)⁻¹) := by
          simp [habc]
    _ = (u * v) * (b * c)⁻¹ := by
          -- Cancel `a` using `a * a⁻¹ = 1`.
          -- We use commutativity to bring `a` next to `a⁻¹`.
          have : (a * u * v) * (a⁻¹ * (b * c)⁻¹) = (a * a⁻¹) * (u * v) * (b * c)⁻¹ := by
            ac_rfl
          simp [this, ENNReal.mul_inv_cancel ha0 hat]
    _ = (u * b⁻¹) * (v * c⁻¹) := by
          -- Expand `(b*c)⁻¹` and regroup.
          simp [hbc]
          ac_rfl
    _ = P4 m x * P4 n y := by
          -- Unfold `P4` on the RHS.
          simp [P4, div_eq_mul_inv, b, c, u, v, mul_assoc]

/-! ## 2-dependence factorization identity for `q = 3` -/

private lemma denom3_factorization (m n : ℕ) :
    Nat.choose (m + n + 4) (m + 2) * denom3 m * denom3 n = denom3 (m + 2 + n) := by
  -- Use `choose_mul_factorial_mul_factorial`.
  have hle : m + 2 ≤ m + n + 4 := by omega
  have hsub : m + n + 4 - (m + 2) = n + 2 := by omega
  have hchoose :
      Nat.choose (m + n + 4) (m + 2) * Nat.factorial (m + 2) * Nat.factorial (n + 2)
        = Nat.factorial (m + n + 4) := by
    -- `choose n k * k! * (n-k)! = n!`
    simpa [hsub, Nat.mul_assoc] using
      (Nat.choose_mul_factorial_mul_factorial (n := m + n + 4) (k := m + 2) hle)
  -- Rewrite in terms of `denom3`.
  simpa [denom3, Nat.add_assoc, Nat.add_left_comm, Nat.add_comm, Nat.mul_assoc] using hchoose

/-- The `q = 3` analogue of equation (10) in the paper: sum over the two inserted letters. -/
theorem sum_P3_insert2 (m n : ℕ) (x : Word 3 m) (y : Word 3 n) :
    (∑ a : Fin 3, ∑ b : Fin 3, P3 (m + 2 + n) (insert2 (q := 3) (m := m) (n := n) x a b y))
      = P3 m x * P3 n y := by
  classical
  -- Start from Proposition 11 on `B`.
  have hB := sum_B_insert2_three (x := x) (y := y) (m := m) (n := n)
  -- Cast to `ℝ≥0∞`.
  have hB' :
      (∑ a : Fin 3, ∑ b : Fin 3,
          (B (q := 3) (insert2 (q := 3) (m := m) (n := n) x a b y) : ℝ≥0∞))
        = (2 * Nat.choose (m + n + 4) (m + 2) * B (q := 3) x * B (q := 3) y : ℝ≥0∞) := by
    exact_mod_cast hB
  -- Denominator factorization.
  have hden :
      (Nat.choose (m + n + 4) (m + 2) * denom3 m * denom3 n : ℝ≥0∞)
        = (denom3 (m + 2 + n) : ℝ≥0∞) := by
    exact_mod_cast (denom3_factorization m n)

  -- Compute the LHS using `hB'` and simplify.
  -- First pull out the constant factors `2` and `(denom3 (m+2+n))⁻¹`.
  have hL :
      (∑ a : Fin 3, ∑ b : Fin 3, P3 (m + 2 + n) (insert2 (q := 3) (m := m) (n := n) x a b y))
        =
        (2 * (∑ a : Fin 3, ∑ b : Fin 3,
            (B (q := 3) (insert2 (q := 3) (m := m) (n := n) x a b y) : ℝ≥0∞)))
          * (denom3 (m + 2 + n) : ℝ≥0∞)⁻¹ := by
    simp [P3, div_eq_mul_inv, Finset.mul_sum, mul_left_comm, mul_comm]

  -- Now expand both sides and cancel the normalizing factors.
  let aNat : ℕ := Nat.choose (m + n + 4) (m + 2)
  let a : ℝ≥0∞ := (aNat : ℝ≥0∞)
  let b : ℝ≥0∞ := (denom3 m : ℝ≥0∞)
  let c : ℝ≥0∞ := (denom3 n : ℝ≥0∞)
  let u : ℝ≥0∞ := (B (q := 3) x : ℝ≥0∞)
  let v : ℝ≥0∞ := (B (q := 3) y : ℝ≥0∞)
  let d : ℝ≥0∞ := (denom3 (m + 2 + n) : ℝ≥0∞)

  have ha_pos : 0 < aNat := by
    have hle : m + 2 ≤ m + n + 4 := by omega
    exact Nat.choose_pos hle
  have ha0 : a ≠ 0 := by
    have : (aNat : ℝ≥0∞) ≠ 0 := by
      exact_mod_cast (Nat.ne_of_gt ha_pos)
    simpa [a] using this
  have hat : a ≠ ⊤ := by simp [a]
  have hbtop : b ≠ ⊤ := denom3_ne_top m
  have hctop : c ≠ ⊤ := denom3_ne_top n

  -- Rewrite `d` as `a * b * c` using `hden`.
  have hd : d = a * b * c := by
    -- `hden` gives `(aNat * denom3 m * denom3 n : ℝ≥0∞) = d`.
    have : d = (aNat * denom3 m * denom3 n : ℝ≥0∞) := by
      simpa [d] using hden.symm
    -- Rewrite casts of naturals as products in `ℝ≥0∞`.
    simpa [aNat, a, b, c, Nat.cast_mul, Nat.mul_assoc, Nat.mul_left_comm, Nat.mul_comm, mul_assoc] using this

  have habc : (a * b * c)⁻¹ = a⁻¹ * (b * c)⁻¹ := by
    -- `a*b*c = a*(b*c)` and apply `ENNReal.mul_inv`.
    have h : a * b * c = a * (b * c) := by ac_rfl
    simpa [h] using
      (ENNReal.mul_inv (a := a) (b := (b * c))
        (Or.inr (ENNReal.mul_ne_top hbtop hctop)) (Or.inl hat))

  calc
    (∑ a' : Fin 3, ∑ b' : Fin 3, P3 (m + 2 + n) (insert2 (q := 3) (m := m) (n := n) x a' b' y))
        = (2 * (2 * a * u * v)) * d⁻¹ := by
            -- Use `hL` and rewrite the `B`-sum using `hB'`.
            have hB'' :
                (∑ a' : Fin 3, ∑ b' : Fin 3,
                    (B (q := 3) (insert2 (q := 3) (m := m) (n := n) x a' b' y) : ℝ≥0∞))
                  = 2 * a * u * v := by
              simpa [aNat, a, u, v, Nat.cast_mul, mul_assoc, mul_left_comm, mul_comm] using hB'
            -- Substitute.
            simp [hL, hB'', d]
    _ = (4 * u * v) * (b * c)⁻¹ := by
          -- Rewrite `d` and cancel `a`.
          have hcancel :
              (2 * (2 * a * u * v)) * d⁻¹
                = (4 * a * u * v) * (a * b * c)⁻¹ := by
                    -- expand `d` using `hd` and combine the numeric factors
                    have h4 : (4 : ℝ≥0∞) = (2 : ℝ≥0∞) * 2 := by
                      norm_num
                    -- rewrite `d` and reassociate
                    simp [hd, d, h4, mul_assoc]
          -- Now expand `(a*b*c)⁻¹` and cancel `a`.
          have hcancel' :
              (4 * a * u * v) * (a * b * c)⁻¹ = (4 * u * v) * (b * c)⁻¹ := by
            -- rewrite inverse of the product and regroup to `a * a⁻¹`.
            have hrewrite :
                (4 * a * u * v) * (a * b * c)⁻¹ = (4 * a * u * v) * (a⁻¹ * (b * c)⁻¹) := by
              simp [habc]
            -- cancel `a`
            calc
              (4 * a * u * v) * (a * b * c)⁻¹
                  = (4 * a * u * v) * (a⁻¹ * (b * c)⁻¹) := hrewrite
              _ = (4 * u * v) * (b * c)⁻¹ := by
                    -- regroup as `a * a⁻¹` and cancel
                    have hgroup :
                        (4 * a * u * v) * (a⁻¹ * (b * c)⁻¹) =
                          (a * a⁻¹) * (4 * u * v) * (b * c)⁻¹ := by
                        ac_rfl
                    -- rewrite using `hgroup`, then use `a * a⁻¹ = 1`
                    rw [hgroup]
                    simp [ENNReal.mul_inv_cancel ha0 hat, mul_assoc]
          -- finish
          exact Eq.trans hcancel hcancel'
    _ = P3 m x * P3 n y := by
          -- Unfold `P3` on the RHS.
          have h4 : (4 : ℝ≥0∞) = (2 : ℝ≥0∞) * 2 := by
            norm_num
          have hbc : (b * c)⁻¹ = b⁻¹ * c⁻¹ :=
            ENNReal.mul_inv (a := b) (b := c) (Or.inr hctop) (Or.inl hbtop)
          -- `P3 m x * P3 n y = (4 * u * v) * (b * c)⁻¹`.
          simp [P3, div_eq_mul_inv, u, v, b, c, h4, hbc, mul_assoc, mul_left_comm]

end Word

end FiniteDependence.Coloring

end
