import Mathlib

namespace FiniteDependence.MIS

/-!
## k=5: algebraic elimination from the compatibility polynomials f(p,t), g(p,t)

From the computational checks we obtain two relations `f(p,t)=0` (length 16) and
`g(p,t)=0` (length 20). The polynomial `g` is linear in `t`, so we can solve for
`t` as a rational function of `p`. Substituting into `f` yields the quartic
factorization `A(p) * B(p) = 0`.
-/

namespace K5Elim

variable {K : Type} [Field K]

def f (p t : K) : K :=
  (-3 : K) * p ^ 4 + (-20 : K) * p ^ 3 + 6 * p ^ 2 * t + (-48 : K) * p ^ 2 +
    30 * p * t + 45 * p + (-3 : K) * t ^ 2 + (-12 : K) * t - 9

def g (p t : K) : K :=
  (-25 : K) * p ^ 4 + (-60 : K) * p ^ 3 + 30 * p ^ 2 * t + (-60 : K) * p ^ 2 +
    30 * p * t + 75 * p + (-15 : K) * t - 16

def d (p : K) : K :=
  2 * p ^ 2 + 2 * p - 1

def num (p : K) : K :=
  25 * p ^ 4 + 60 * p ^ 3 + 60 * p ^ 2 - 75 * p + 16

def A (p : K) : K :=
  5 * p ^ 4 - 355 * p ^ 3 + 460 * p ^ 2 - 200 * p + 29

def B (p : K) : K :=
  5 * p ^ 4 - 5 * p ^ 3 - 5 * p ^ 2 + 5 * p - 1

/-!
For the two quartic cases `A(p)=0` and `B(p)=0` we will also use explicit *polynomial* formulas
for `t` (i.e. formulas with no denominators depending on `p`).

These are exactly the `t` used in `K5CaseACompute` / `K5CaseBCompute`.
-/

def tA (p : K) : K :=
  ((1 : K) / 177) * ((5 : K) * p ^ 3 + (-208 : K) * p ^ 2 + (705 : K) * p + (-241 : K))

def tB (p : K) : K :=
  ((1 : K) / 3) * ((5 : K) * p ^ 3 + (-7 : K) * p ^ 2 + (10 : K) * p + (-3 : K))

theorem g_eq (p t : K) : g p t = ((15 : K) * d p) * t - num p := by
  simp [g, d, num]
  ring

section

variable [CharZero K]

theorem tA_id (p : K) :
    (177 : K) * (((15 : K) * d p) * tA p - num p) = ((30 : K) * p + 27) * A p := by
  simp [tA, d, num, A]
  ring_nf

theorem tB_id (p : K) :
    (3 : K) * (((15 : K) * d p) * tB p - num p) = ((30 : K) * p + 3) * B p := by
  simp [tB, d, num, B]
  ring_nf

theorem tA_mul_den_eq_num_of_A (p : K) (hA : A p = 0) : ((15 : K) * d p) * tA p = num p := by
  have h177 : (177 : K) ≠ 0 := by norm_num
  have h :
      (177 : K) * (((15 : K) * d p) * tA p - num p) = 0 := by
    simpa [hA] using (tA_id (K := K) (p := p))
  have h' : ((15 : K) * d p) * tA p - num p = 0 := (mul_eq_zero.mp h).resolve_left h177
  exact sub_eq_zero.mp h'

theorem tB_mul_den_eq_num_of_B (p : K) (hB : B p = 0) : ((15 : K) * d p) * tB p = num p := by
  have h3 : (3 : K) ≠ 0 := by norm_num
  have h :
      (3 : K) * (((15 : K) * d p) * tB p - num p) = 0 := by
    simpa [hB] using (tB_id (K := K) (p := p))
  have h' : ((15 : K) * d p) * tB p - num p = 0 := (mul_eq_zero.mp h).resolve_left h3
  exact sub_eq_zero.mp h'

theorem solve_t (p t : K) (hg : g p t = 0) (hd : d p ≠ 0) :
    t = num p / ((15 : K) * d p) := by
  have h15 : (15 : K) ≠ 0 := by norm_num
  have hden : ((15 : K) * d p) ≠ 0 := mul_ne_zero h15 hd
  have hsub : ((15 : K) * d p) * t - num p = 0 := by
    simpa [g_eq (p := p) (t := t)] using hg
  have hmul : ((15 : K) * d p) * t = num p := sub_eq_zero.mp hsub
  -- `eq_div_iff` expects `t * denom = num`.
  have hmul' : t * ((15 : K) * d p) = num p := by
    simpa [mul_comm, mul_left_comm, mul_assoc] using hmul
  exact (eq_div_iff hden).2 hmul'

theorem f_subst (p : K) (hd : d p ≠ 0) :
    (((15 : K) * d p) ^ 2) * f p (num p / ((15 : K) * d p)) =
      (-3 : K) * A p * B p := by
  have h15 : (15 : K) ≠ 0 := by norm_num
  have hden : ((15 : K) * d p) ≠ 0 := mul_ne_zero h15 hd
  -- Expand the polynomials, then clear the (single) rational-function denominator.
  simp [f, num, A, B]
  field_simp [hden, hd]
  simp [d]
  ring_nf

theorem AB_eq_zero_of_fg (p t : K) (hf : f p t = 0) (hg : g p t = 0) (hd : d p ≠ 0) :
    A p * B p = 0 := by
  have ht : t = num p / ((15 : K) * d p) := solve_t (p := p) (t := t) hg hd
  have hf' : f p (num p / ((15 : K) * d p)) = 0 := by simpa [ht] using hf
  have hmul : (-3 : K) * A p * B p = 0 := by
    -- Multiply `hf'` by the common denominator square and rewrite using `f_subst`.
    have : (((15 : K) * d p) ^ 2) * f p (num p / ((15 : K) * d p)) = 0 := by
      simp [hf']
    simpa [f_subst (p := p) (hd := hd)] using this
  have h3 : (-3 : K) ≠ 0 := by norm_num
  -- Cancel the nonzero scalar `-3`.
  have : (-3 : K) * (A p * B p) = 0 := by
    simpa [mul_assoc] using hmul
  exact (mul_eq_zero.mp this).resolve_left h3

theorem t_eq_tA_of_gA (p t : K) (hg : g p t = 0) (hA : A p = 0) (hd : d p ≠ 0) :
    t = tA p := by
  have h15 : (15 : K) ≠ 0 := by norm_num
  have hden : ((15 : K) * d p) ≠ 0 := mul_ne_zero h15 hd
  have ht : t = num p / ((15 : K) * d p) := solve_t (p := p) (t := t) hg hd
  have hmul : ((15 : K) * d p) * tA p = num p := tA_mul_den_eq_num_of_A (K := K) (p := p) hA
  have htA : tA p = num p / ((15 : K) * d p) := by
    -- `eq_div_iff` expects `tA * denom = num`.
    refine (eq_div_iff hden).2 ?_
    simpa [mul_comm, mul_left_comm, mul_assoc] using hmul
  simpa [htA] using ht

theorem t_eq_tB_of_gB (p t : K) (hg : g p t = 0) (hB : B p = 0) (hd : d p ≠ 0) :
    t = tB p := by
  have h15 : (15 : K) ≠ 0 := by norm_num
  have hden : ((15 : K) * d p) ≠ 0 := mul_ne_zero h15 hd
  have ht : t = num p / ((15 : K) * d p) := solve_t (p := p) (t := t) hg hd
  have hmul : ((15 : K) * d p) * tB p = num p := tB_mul_den_eq_num_of_B (K := K) (p := p) hB
  have htB : tB p = num p / ((15 : K) * d p) := by
    refine (eq_div_iff hden).2 ?_
    simpa [mul_comm, mul_left_comm, mul_assoc] using hmul
  simpa [htB] using ht

end

end K5Elim

end FiniteDependence.MIS
