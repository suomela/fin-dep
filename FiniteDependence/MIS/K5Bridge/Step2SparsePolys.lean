import FiniteDependence.MIS.K5Bridge.SparseCertStep2Data
import FiniteDependence.MIS.K5Bridge.Step2SparseRows
import FiniteDependence.MIS.K5Bridge.Step3SparseCore
import FiniteDependence.MIS.K5Elim

namespace FiniteDependence.MIS

namespace K5Bridge

open MeasureTheory Set
open scoped ProbabilityTheory

namespace Model

open FiniteDependence.MIS.Model

noncomputable section

namespace Step2Sparse

open Step3

private theorem prob_prefix_eq_eval_cert (μ : Measure FiniteDependence.MIS.State) [IsProbabilityMeasure μ]
    (hstat : Stationary μ) (hdep : KDependent 5 μ)
    {m : Nat} {x : String} (hx : x ∈ K5Data.allowedWords m)
    (hm : m ≤ 14)
    (cert : List (Nat × ℚ)) (hmatch : certificateMatches x cert = true) :
    FiniteDependence.MIS.Model.prob μ (cylStr (a := (0 : ℤ)) x) =
      Poly3.eval (pVal μ) (tVal μ) 0 (certPoly cert) := by
  exact
    prob_prefix_eq_eval_certPoly (μ := μ) hstat hdep (m := m) (x := x)
      hx hm cert hmatch

theorem prob_1_eq_eval (μ : Measure FiniteDependence.MIS.State) [IsProbabilityMeasure μ]
    (hstat : Stationary μ) (hdep : KDependent 5 μ) :
    FiniteDependence.MIS.Model.prob μ (cylStr (a := (0 : ℤ)) "1") =
      Poly3.eval (pVal μ) (tVal μ) 0 (certPoly cert_1) := by
  simpa using
    prob_prefix_eq_eval_cert (μ := μ) hstat hdep
      (m := 1) (x := "1") (hx := by native_decide) (hm := by decide) cert_1 cert_1_matches

theorem prob_0010100101_eq_eval (μ : Measure FiniteDependence.MIS.State) [IsProbabilityMeasure μ]
    (hstat : Stationary μ) (hdep : KDependent 5 μ) :
    FiniteDependence.MIS.Model.prob μ (cylStr (a := (0 : ℤ)) "0010100101") =
      Poly3.eval (pVal μ) (tVal μ) 0 (certPoly cert_0010100101) := by
  simpa using
    prob_prefix_eq_eval_cert (μ := μ) hstat hdep
      (m := 10) (x := "0010100101") (hx := by native_decide)
      (hm := by decide) cert_0010100101 cert_0010100101_matches

theorem prob_100_eq_eval (μ : Measure FiniteDependence.MIS.State) [IsProbabilityMeasure μ]
    (hstat : Stationary μ) (hdep : KDependent 5 μ) :
    FiniteDependence.MIS.Model.prob μ (cylStr (a := (0 : ℤ)) "100") =
      Poly3.eval (pVal μ) (tVal μ) 0 (certPoly cert_100) := by
  simpa using
    prob_prefix_eq_eval_cert (μ := μ) hstat hdep
      (m := 3) (x := "100") (hx := by native_decide) (hm := by decide) cert_100 cert_100_matches

theorem prob_10100101_eq_eval (μ : Measure FiniteDependence.MIS.State) [IsProbabilityMeasure μ]
    (hstat : Stationary μ) (hdep : KDependent 5 μ) :
    FiniteDependence.MIS.Model.prob μ (cylStr (a := (0 : ℤ)) "10100101") =
      Poly3.eval (pVal μ) (tVal μ) 0 (certPoly cert_10100101) := by
  simpa using
    prob_prefix_eq_eval_cert (μ := μ) hstat hdep
      (m := 8) (x := "10100101") (hx := by native_decide)
      (hm := by decide) cert_10100101 cert_10100101_matches

theorem prob_10100_eq_eval (μ : Measure FiniteDependence.MIS.State) [IsProbabilityMeasure μ]
    (hstat : Stationary μ) (hdep : KDependent 5 μ) :
    FiniteDependence.MIS.Model.prob μ (cylStr (a := (0 : ℤ)) "10100") =
      Poly3.eval (pVal μ) (tVal μ) 0 (certPoly cert_10100) := by
  simpa using
    prob_prefix_eq_eval_cert (μ := μ) hstat hdep
      (m := 5) (x := "10100") (hx := by native_decide)
      (hm := by decide) cert_10100 cert_10100_matches

theorem prob_001001_eq_eval (μ : Measure FiniteDependence.MIS.State) [IsProbabilityMeasure μ]
    (hstat : Stationary μ) (hdep : KDependent 5 μ) :
    FiniteDependence.MIS.Model.prob μ (cylStr (a := (0 : ℤ)) "001001") =
      Poly3.eval (pVal μ) (tVal μ) 0 (certPoly cert_001001) := by
  simpa using
    prob_prefix_eq_eval_cert (μ := μ) hstat hdep
      (m := 6) (x := "001001") (hx := by native_decide)
      (hm := by decide) cert_001001 cert_001001_matches

theorem prob_100101_eq_eval (μ : Measure FiniteDependence.MIS.State) [IsProbabilityMeasure μ]
    (hstat : Stationary μ) (hdep : KDependent 5 μ) :
    FiniteDependence.MIS.Model.prob μ (cylStr (a := (0 : ℤ)) "100101") =
      Poly3.eval (pVal μ) (tVal μ) 0 (certPoly cert_100101) := by
  simpa using
    prob_prefix_eq_eval_cert (μ := μ) hstat hdep
      (m := 6) (x := "100101") (hx := by native_decide)
      (hm := by decide) cert_100101 cert_100101_matches

theorem prob_100100_eq_eval (μ : Measure FiniteDependence.MIS.State) [IsProbabilityMeasure μ]
    (hstat : Stationary μ) (hdep : KDependent 5 μ) :
    FiniteDependence.MIS.Model.prob μ (cylStr (a := (0 : ℤ)) "100100") =
      Poly3.eval (pVal μ) (tVal μ) 0 (certPoly cert_100100) := by
  simpa using
    prob_prefix_eq_eval_cert (μ := μ) hstat hdep
      (m := 6) (x := "100100") (hx := by native_decide)
      (hm := by decide) cert_100100 cert_100100_matches

theorem prob_00101_eq_eval (μ : Measure FiniteDependence.MIS.State) [IsProbabilityMeasure μ]
    (hstat : Stationary μ) (hdep : KDependent 5 μ) :
    FiniteDependence.MIS.Model.prob μ (cylStr (a := (0 : ℤ)) "00101") =
      Poly3.eval (pVal μ) (tVal μ) 0 (certPoly cert_00101) := by
  simpa using
    prob_prefix_eq_eval_cert (μ := μ) hstat hdep
      (m := 5) (x := "00101") (hx := by native_decide)
      (hm := by decide) cert_00101 cert_00101_matches

theorem prob_101_eq_eval (μ : Measure FiniteDependence.MIS.State) [IsProbabilityMeasure μ]
    (hstat : Stationary μ) (hdep : KDependent 5 μ) :
    FiniteDependence.MIS.Model.prob μ (cylStr (a := (0 : ℤ)) "101") =
      Poly3.eval (pVal μ) (tVal μ) 0 (certPoly cert_101) := by
  simpa [cert_101, cert_101_matches] using
    prob_prefix_eq_eval_cert (μ := μ) hstat hdep
      (m := 3) (x := "101") (hx := by native_decide)
      (hm := by decide) cert_101 cert_101_matches

theorem prob_1010010101_eq_eval (μ : Measure FiniteDependence.MIS.State) [IsProbabilityMeasure μ]
    (hstat : Stationary μ) (hdep : KDependent 5 μ) :
    FiniteDependence.MIS.Model.prob μ (cylStr (a := (0 : ℤ)) "1010010101") =
      Poly3.eval (pVal μ) (tVal μ) 0 (certPoly cert_1010010101) := by
  simpa using
    prob_prefix_eq_eval_cert (μ := μ) hstat hdep
      (m := 10) (x := "1010010101") (hx := by native_decide)
      (hm := by decide) cert_1010010101 cert_1010010101_matches

theorem prob_00100_eq_eval (μ : Measure FiniteDependence.MIS.State) [IsProbabilityMeasure μ]
    (hstat : Stationary μ) (hdep : KDependent 5 μ) :
    FiniteDependence.MIS.Model.prob μ (cylStr (a := (0 : ℤ)) "00100") =
      Poly3.eval (pVal μ) (tVal μ) 0 (certPoly cert_00100) := by
  simpa using
    prob_prefix_eq_eval_cert (μ := μ) hstat hdep
      (m := 5) (x := "00100") (hx := by native_decide)
      (hm := by decide) cert_00100 cert_00100_matches

theorem prob_1010010100_eq_eval (μ : Measure FiniteDependence.MIS.State) [IsProbabilityMeasure μ]
    (hstat : Stationary μ) (hdep : KDependent 5 μ) :
    FiniteDependence.MIS.Model.prob μ (cylStr (a := (0 : ℤ)) "1010010100") =
      Poly3.eval (pVal μ) (tVal μ) 0 (certPoly cert_1010010100) := by
  simpa using
    prob_prefix_eq_eval_cert (μ := μ) hstat hdep
      (m := 10) (x := "1010010100") (hx := by native_decide)
      (hm := by decide) cert_1010010100 cert_1010010100_matches

theorem prob_00100100_eq_eval (μ : Measure FiniteDependence.MIS.State) [IsProbabilityMeasure μ]
    (hstat : Stationary μ) (hdep : KDependent 5 μ) :
    FiniteDependence.MIS.Model.prob μ (cylStr (a := (0 : ℤ)) "00100100") =
      Poly3.eval (pVal μ) (tVal μ) 0 (certPoly cert_00100100) := by
  simpa using
    prob_prefix_eq_eval_cert (μ := μ) hstat hdep
      (m := 8) (x := "00100100") (hx := by native_decide)
      (hm := by decide) cert_00100100 cert_00100100_matches

theorem prob_0010100_eq_eval (μ : Measure FiniteDependence.MIS.State) [IsProbabilityMeasure μ]
    (hstat : Stationary μ) (hdep : KDependent 5 μ) :
    FiniteDependence.MIS.Model.prob μ (cylStr (a := (0 : ℤ)) "0010100") =
      Poly3.eval (pVal μ) (tVal μ) 0 (certPoly cert_0010100) := by
  simpa using
    prob_prefix_eq_eval_cert (μ := μ) hstat hdep
      (m := 7) (x := "0010100") (hx := by native_decide)
      (hm := by decide) cert_0010100 cert_0010100_matches

theorem prob_0010010100_eq_eval (μ : Measure FiniteDependence.MIS.State) [IsProbabilityMeasure μ]
    (hstat : Stationary μ) (hdep : KDependent 5 μ) :
    FiniteDependence.MIS.Model.prob μ (cylStr (a := (0 : ℤ)) "0010010100") =
      Poly3.eval (pVal μ) (tVal μ) 0 (certPoly cert_0010010100) := by
  simpa using
    prob_prefix_eq_eval_cert (μ := μ) hstat hdep
      (m := 10) (x := "0010010100") (hx := by native_decide)
      (hm := by decide) cert_0010010100 cert_0010010100_matches

theorem prob_0010010100100_eq_eval (μ : Measure FiniteDependence.MIS.State) [IsProbabilityMeasure μ]
    (hstat : Stationary μ) (hdep : KDependent 5 μ) :
    FiniteDependence.MIS.Model.prob μ (cylStr (a := (0 : ℤ)) "0010010100100") =
      Poly3.eval (pVal μ) (tVal μ) 0 (certPoly cert_0010010100100) := by
  simpa using
    prob_prefix_eq_eval_cert (μ := μ) hstat hdep
      (m := 13) (x := "0010010100100") (hx := by native_decide)
      (hm := by decide) cert_0010010100100 cert_0010010100100_matches

theorem prob_00_eq_eval (μ : Measure FiniteDependence.MIS.State) [IsProbabilityMeasure μ]
    (hstat : Stationary μ) (hdep : KDependent 5 μ) :
    FiniteDependence.MIS.Model.prob μ (cylStr (a := (0 : ℤ)) "00") =
      Poly3.eval (pVal μ) (tVal μ) 0 (certPoly cert_00) := by
  simpa using
    prob_prefix_eq_eval_cert (μ := μ) hstat hdep
      (m := 2) (x := "00") (hx := by native_decide)
      (hm := by decide) cert_00 cert_00_matches

def fSparsePoly : Poly3.Poly :=
  certPoly cert_1 * certPoly cert_0010100101 -
    certPoly cert_100 * certPoly cert_10100101 +
      certPoly cert_10100 * certPoly cert_001001 -
        certPoly cert_10100 * certPoly cert_100101 +
          certPoly cert_100100 * certPoly cert_00101 +
            certPoly cert_10100101 * certPoly cert_101 -
              certPoly cert_1010010101 * certPoly cert_1

def rSparsePoly : Poly3.Poly :=
  -(certPoly cert_00100 * certPoly cert_1010010100) +
    certPoly cert_00100100 * certPoly cert_0010100 +
      certPoly cert_0010010100 * certPoly cert_10100 -
        certPoly cert_0010010100100 * certPoly cert_00

def fExpectedPoly : Poly3.Poly :=
  ((-3 : ℚ) • (pPoly ^ 4)) + ((-20 : ℚ) • (pPoly ^ 3)) + ((6 : ℚ) • ((pPoly ^ 2) * tPoly)) +
    ((-48 : ℚ) • (pPoly ^ 2)) + ((30 : ℚ) • (pPoly * tPoly)) + ((45 : ℚ) • pPoly) +
      ((-3 : ℚ) • (tPoly ^ 2)) + ((-12 : ℚ) • tPoly) + ((-9 : ℚ) • (1 : Poly3.Poly))

def rExpectedPoly : Poly3.Poly :=
  ((-16 : ℚ) • (pPoly ^ 4)) + ((12 : ℚ) • ((pPoly ^ 2) * tPoly)) + ((84 : ℚ) • (pPoly ^ 2)) +
    ((-60 : ℚ) • (pPoly * tPoly)) + ((-60 : ℚ) • pPoly) + ((9 : ℚ) • (tPoly ^ 2)) +
      ((21 : ℚ) • tPoly) + ((11 : ℚ) • (1 : Poly3.Poly))

def rCompat (p t : ℝ) : ℝ :=
  (-16 : ℝ) * p ^ 4 + 12 * p ^ 2 * t + 84 * p ^ 2 + (-60 : ℝ) * p * t + (-60 : ℝ) * p +
    9 * t ^ 2 + 21 * t + 11

theorem fSparsePoly_eq : fSparsePoly = fExpectedPoly := by
  native_decide

theorem rSparsePoly_eq : rSparsePoly = rExpectedPoly := by
  native_decide

theorem eval_fSparsePoly_eq_zero (μ : Measure FiniteDependence.MIS.State) [IsProbabilityMeasure μ]
    (hstat : Stationary μ) (hdep : KDependent 5 μ) :
    Poly3.eval (pVal μ) (tVal μ) 0 fSparsePoly = 0 := by
  have hrow := f_row_combination_zero (μ := μ) hstat hdep
  have hrow' :
      FiniteDependence.MIS.Model.prob μ (cylStr (a := (0 : ℤ)) "1") *
          FiniteDependence.MIS.Model.prob μ (cylStr (a := (0 : ℤ)) "0010100101") -
        FiniteDependence.MIS.Model.prob μ (cylStr (a := (0 : ℤ)) "100") *
          FiniteDependence.MIS.Model.prob μ (cylStr (a := (0 : ℤ)) "10100101") +
        FiniteDependence.MIS.Model.prob μ (cylStr (a := (0 : ℤ)) "10100") *
          FiniteDependence.MIS.Model.prob μ (cylStr (a := (0 : ℤ)) "001001") -
        FiniteDependence.MIS.Model.prob μ (cylStr (a := (0 : ℤ)) "10100") *
          FiniteDependence.MIS.Model.prob μ (cylStr (a := (0 : ℤ)) "100101") +
        FiniteDependence.MIS.Model.prob μ (cylStr (a := (0 : ℤ)) "100100") *
          FiniteDependence.MIS.Model.prob μ (cylStr (a := (0 : ℤ)) "00101") +
        FiniteDependence.MIS.Model.prob μ (cylStr (a := (0 : ℤ)) "10100101") *
          FiniteDependence.MIS.Model.prob μ (cylStr (a := (0 : ℤ)) "101") -
        FiniteDependence.MIS.Model.prob μ (cylStr (a := (0 : ℤ)) "1010010101") *
          FiniteDependence.MIS.Model.prob μ (cylStr (a := (0 : ℤ)) "1") = 0 := by
    simpa using hrow
  simp_rw [prob_1_eq_eval (μ := μ) hstat hdep,
    prob_0010100101_eq_eval (μ := μ) hstat hdep,
    prob_100_eq_eval (μ := μ) hstat hdep,
    prob_10100101_eq_eval (μ := μ) hstat hdep,
    prob_10100_eq_eval (μ := μ) hstat hdep,
    prob_001001_eq_eval (μ := μ) hstat hdep,
    prob_100101_eq_eval (μ := μ) hstat hdep,
    prob_100100_eq_eval (μ := μ) hstat hdep,
    prob_00101_eq_eval (μ := μ) hstat hdep,
    prob_101_eq_eval (μ := μ) hstat hdep,
    prob_1010010101_eq_eval (μ := μ) hstat hdep] at hrow'
  simpa [fSparsePoly, Poly3.eval_add, Poly3.eval_sub, Poly3.eval_mul] using hrow'

theorem eval_rSparsePoly_eq_zero (μ : Measure FiniteDependence.MIS.State) [IsProbabilityMeasure μ]
    (hstat : Stationary μ) (hdep : KDependent 5 μ) :
    Poly3.eval (pVal μ) (tVal μ) 0 rSparsePoly = 0 := by
  have hrow := r_row_combination_zero (μ := μ) hstat hdep
  have hrow' :
      -(FiniteDependence.MIS.Model.prob μ (cylStr (a := (0 : ℤ)) "00100") *
          FiniteDependence.MIS.Model.prob μ (cylStr (a := (0 : ℤ)) "1010010100")) +
        FiniteDependence.MIS.Model.prob μ (cylStr (a := (0 : ℤ)) "00100100") *
          FiniteDependence.MIS.Model.prob μ (cylStr (a := (0 : ℤ)) "0010100") +
        FiniteDependence.MIS.Model.prob μ (cylStr (a := (0 : ℤ)) "0010010100") *
          FiniteDependence.MIS.Model.prob μ (cylStr (a := (0 : ℤ)) "10100") -
        FiniteDependence.MIS.Model.prob μ (cylStr (a := (0 : ℤ)) "0010010100100") *
          FiniteDependence.MIS.Model.prob μ (cylStr (a := (0 : ℤ)) "00") = 0 := by
    simpa using hrow
  simp_rw [prob_00100_eq_eval (μ := μ) hstat hdep,
    prob_1010010100_eq_eval (μ := μ) hstat hdep,
    prob_00100100_eq_eval (μ := μ) hstat hdep,
    prob_0010100_eq_eval (μ := μ) hstat hdep,
    prob_0010010100_eq_eval (μ := μ) hstat hdep,
    prob_10100_eq_eval (μ := μ) hstat hdep,
    prob_0010010100100_eq_eval (μ := μ) hstat hdep,
    prob_00_eq_eval (μ := μ) hstat hdep] at hrow'
  simpa [rSparsePoly, Poly3.eval_add, Poly3.eval_sub, Poly3.eval_mul, Poly3.eval_neg] using hrow'

theorem f_eq_zero_prob (μ : Measure FiniteDependence.MIS.State) [IsProbabilityMeasure μ]
    (hstat : Stationary μ) (hdep : KDependent 5 μ) :
    K5Elim.f (K := ℝ) (pVal μ) (tVal μ) = 0 := by
  have h0 : Poly3.eval (pVal μ) (tVal μ) 0 fSparsePoly = 0 :=
    eval_fSparsePoly_eq_zero (μ := μ) hstat hdep
  have h1 : Poly3.eval (pVal μ) (tVal μ) 0 fExpectedPoly = 0 := by
    simpa [fSparsePoly_eq] using h0
  have hEval :
      Poly3.eval (pVal μ) (tVal μ) 0 fExpectedPoly =
        K5Elim.f (K := ℝ) (pVal μ) (tVal μ) := by
    simp [fExpectedPoly, pPoly, tPoly, K5Elim.f,
      Poly3.eval_add, Poly3.eval_sub, Poly3.eval_mul, Poly3.eval_smul, Poly3.eval_pow,
      Poly3.eval_varP, Poly3.eval_varT, Poly3.eval_const]
    ring_nf
  simpa [hEval] using h1

theorem rCompat_eq_zero_prob (μ : Measure FiniteDependence.MIS.State) [IsProbabilityMeasure μ]
    (hstat : Stationary μ) (hdep : KDependent 5 μ) :
    rCompat (pVal μ) (tVal μ) = 0 := by
  have h0 : Poly3.eval (pVal μ) (tVal μ) 0 rSparsePoly = 0 :=
    eval_rSparsePoly_eq_zero (μ := μ) hstat hdep
  have h1 : Poly3.eval (pVal μ) (tVal μ) 0 rExpectedPoly = 0 := by
    simpa [rSparsePoly_eq] using h0
  have hEval :
      Poly3.eval (pVal μ) (tVal μ) 0 rExpectedPoly =
        rCompat (pVal μ) (tVal μ) := by
    simp [rExpectedPoly, pPoly, tPoly, rCompat,
      Poly3.eval_add, Poly3.eval_sub, Poly3.eval_mul, Poly3.eval_smul, Poly3.eval_pow,
      Poly3.eval_varP, Poly3.eval_varT, Poly3.eval_const]
    ring_nf
  simpa [hEval] using h1

theorem g_eq_zero_prob (μ : Measure FiniteDependence.MIS.State) [IsProbabilityMeasure μ]
    (hstat : Stationary μ) (hdep : KDependent 5 μ) :
    K5Elim.g (K := ℝ) (pVal μ) (tVal μ) = 0 := by
  have hf : K5Elim.f (K := ℝ) (pVal μ) (tVal μ) = 0 := f_eq_zero_prob (μ := μ) hstat hdep
  have hr : rCompat (pVal μ) (tVal μ) = 0 := rCompat_eq_zero_prob (μ := μ) hstat hdep
  have hg : K5Elim.g (K := ℝ) (pVal μ) (tVal μ) =
      3 * K5Elim.f (K := ℝ) (pVal μ) (tVal μ) + rCompat (pVal μ) (tVal μ) := by
    simp [K5Elim.g, K5Elim.f, rCompat]
    ring_nf
  linarith [hf, hr, hg]

end Step2Sparse

end

end Model

end K5Bridge

end FiniteDependence.MIS
