import FiniteDependence.MIS.K5Bridge.Step2SparsePolys
import FiniteDependence.MIS.K5Bridge.StepLemmas

namespace FiniteDependence.MIS

namespace K5Bridge

open MeasureTheory Set
open scoped ProbabilityTheory

namespace Model

open FiniteDependence.MIS.Model

noncomputable section

namespace Step4Sparse

open Step3 Step2Sparse

private def cert_001010010100 : List (Nat × ℚ) :=
  [(66, (-1 : ℚ)), (178, (1 : ℚ))]

private theorem cert_001010010100_matches :
    certificateMatches "001010010100" cert_001010010100 = true := by
  native_decide

private def cert_0101010010101 : List (Nat × ℚ) :=
  [(86, (-1 : ℚ)), (87, (-1 : ℚ)), (225, (1 : ℚ)), (255, (1 : ℚ))]

private theorem cert_0101010010101_matches :
    certificateMatches "0101010010101" cert_0101010010101 = true := by
  native_decide

private def poly_001010010100 : Poly3.Poly :=
  ((4 : ℚ) • (pPoly ^ 3)) + ((2 : ℚ) • (pPoly ^ 2)) + ((-4 : ℚ) • (pPoly * tPoly)) +
    ((-4 : ℚ) • pPoly) + ((2 : ℚ) • tPoly) + ((1 : ℚ) • (1 : Poly3.Poly))

private theorem certPoly_001010010100_eq :
    certPoly cert_001010010100 = poly_001010010100 := by
  native_decide

private def poly_0101010010101 : Poly3.Poly :=
  ((4 : ℚ) • (pPoly ^ 3)) + ((9 : ℚ) • (pPoly ^ 2)) + ((-4 : ℚ) • (pPoly * tPoly)) +
    ((-4 : ℚ) • pPoly)

private theorem certPoly_0101010010101_eq :
    certPoly cert_0101010010101 = poly_0101010010101 := by
  native_decide

theorem prob_001010010100_eq_formula (μ : Measure FiniteDependence.MIS.State) [IsProbabilityMeasure μ]
    (hstat : Stationary μ) (hdep : KDependent 5 μ) :
    FiniteDependence.MIS.Model.prob μ (cylStr (a := (0 : ℤ)) "001010010100") =
      (2 * pVal μ - 1) * (2 * (pVal μ) ^ 2 + 2 * (pVal μ) - 2 * (tVal μ) - 1) := by
  have hcert :
      FiniteDependence.MIS.Model.prob μ (cylStr (a := (0 : ℤ)) "001010010100") =
        Poly3.eval (pVal μ) (tVal μ) 0 (certPoly cert_001010010100) := by
    simpa using
      prob_prefix_eq_eval_certPoly (μ := μ) hstat hdep
        (m := 12) (x := "001010010100")
        (hx := by native_decide) (hm := by decide)
        (cert := cert_001010010100)
        (hmatch := cert_001010010100_matches)
  calc
    FiniteDependence.MIS.Model.prob μ (cylStr (a := (0 : ℤ)) "001010010100") =
        Poly3.eval (pVal μ) (tVal μ) 0 (certPoly cert_001010010100) := hcert
    _ = Poly3.eval (pVal μ) (tVal μ) 0 poly_001010010100 := by
          simpa [certPoly_001010010100_eq]
    _ = (2 * pVal μ - 1) * (2 * (pVal μ) ^ 2 + 2 * (pVal μ) - 2 * (tVal μ) - 1) := by
          simp [poly_001010010100, pPoly, tPoly, Poly3.eval_add, Poly3.eval_sub, Poly3.eval_mul,
            Poly3.eval_smul, Poly3.eval_pow, Poly3.eval_varP, Poly3.eval_varT, Poly3.eval_const]
          ring_nf

theorem prob_0101010010101_eq_formula (μ : Measure FiniteDependence.MIS.State) [IsProbabilityMeasure μ]
    (hstat : Stationary μ) (hdep : KDependent 5 μ) :
    FiniteDependence.MIS.Model.prob μ (cylStr (a := (0 : ℤ)) "0101010010101") =
      pVal μ * (4 * (pVal μ) ^ 2 + 9 * (pVal μ) - 4 * (tVal μ) - 4) := by
  have hcert :
      FiniteDependence.MIS.Model.prob μ (cylStr (a := (0 : ℤ)) "0101010010101") =
        Poly3.eval (pVal μ) (tVal μ) 0 (certPoly cert_0101010010101) := by
    simpa using
      prob_prefix_eq_eval_certPoly (μ := μ) hstat hdep
        (m := 13) (x := "0101010010101")
        (hx := by native_decide) (hm := by decide)
        (cert := cert_0101010010101)
        (hmatch := cert_0101010010101_matches)
  calc
    FiniteDependence.MIS.Model.prob μ (cylStr (a := (0 : ℤ)) "0101010010101") =
        Poly3.eval (pVal μ) (tVal μ) 0 (certPoly cert_0101010010101) := hcert
    _ = Poly3.eval (pVal μ) (tVal μ) 0 poly_0101010010101 := by
          simpa [certPoly_0101010010101_eq]
    _ = pVal μ * (4 * (pVal μ) ^ 2 + 9 * (pVal μ) - 4 * (tVal μ) - 4) := by
          simp [poly_0101010010101, pPoly, tPoly, Poly3.eval_add, Poly3.eval_sub, Poly3.eval_mul,
            Poly3.eval_smul, Poly3.eval_pow, Poly3.eval_varP, Poly3.eval_varT, Poly3.eval_const]
          ring_nf

private def poly_101 : Poly3.Poly :=
  ((3 : ℚ) • pPoly) + ((-1 : ℚ) • (1 : Poly3.Poly))

private theorem certPoly_101_eq :
    certPoly cert_101 = poly_101 := by
  native_decide

private def poly_0010100 : Poly3.Poly :=
  ((-2 : ℚ) • (pPoly ^ 2)) + ((-7 : ℚ) • pPoly) + ((3 : ℚ) • tPoly) + ((3 : ℚ) • (1 : Poly3.Poly))

private theorem certPoly_0010100_eq :
    certPoly cert_0010100 = poly_0010100 := by
  native_decide

private def poly_10100 : Poly3.Poly :=
  ((-1 : ℚ) • (pPoly ^ 2)) + ((-2 : ℚ) • pPoly) + tPoly + ((1 : ℚ) • (1 : Poly3.Poly))

private theorem certPoly_10100_eq :
    certPoly cert_10100 = poly_10100 := by
  native_decide

private def poly_00100 : Poly3.Poly :=
  (pPoly ^ 2) + ((-1 : ℚ) • tPoly)

private theorem certPoly_00100_eq :
    certPoly cert_00100 = poly_00100 := by
  native_decide

private def poly_10100101 : Poly3.Poly :=
  ((-1 : ℚ) • (pPoly ^ 2)) + ((-10 : ℚ) • pPoly) + ((4 : ℚ) • tPoly) + ((4 : ℚ) • (1 : Poly3.Poly))

private theorem certPoly_10100101_eq :
    certPoly cert_10100101 = poly_10100101 := by
  native_decide

private def poly_00 : Poly3.Poly :=
  ((-2 : ℚ) • pPoly) + ((1 : ℚ) • (1 : Poly3.Poly))

private theorem certPoly_00_eq :
    certPoly cert_00 = poly_00 := by
  native_decide

private theorem prob_101_eq_formula (μ : Measure FiniteDependence.MIS.State) [IsProbabilityMeasure μ]
    (hstat : Stationary μ) (hdep : KDependent 5 μ) :
    FiniteDependence.MIS.Model.prob μ (cylStr (a := (0 : ℤ)) "101") = 3 * pVal μ - 1 := by
  have h := prob_101_eq_eval (μ := μ) hstat hdep
  calc
    FiniteDependence.MIS.Model.prob μ (cylStr (a := (0 : ℤ)) "101") =
        Poly3.eval (pVal μ) (tVal μ) 0 (certPoly cert_101) := h
    _ = Poly3.eval (pVal μ) (tVal μ) 0 poly_101 := by
          simpa [certPoly_101_eq]
    _ = 3 * pVal μ - 1 := by
          simp [poly_101, pPoly, tPoly, Poly3.eval_add, Poly3.eval_sub, Poly3.eval_mul, Poly3.eval_smul,
            Poly3.eval_pow, Poly3.eval_varP, Poly3.eval_varT, Poly3.eval_const]
          ring_nf

private theorem prob_0010100_eq_formula (μ : Measure FiniteDependence.MIS.State) [IsProbabilityMeasure μ]
    (hstat : Stationary μ) (hdep : KDependent 5 μ) :
    FiniteDependence.MIS.Model.prob μ (cylStr (a := (0 : ℤ)) "0010100") =
      (-2) * (pVal μ) ^ 2 + (-7) * pVal μ + 3 * tVal μ + 3 := by
  have h := prob_0010100_eq_eval (μ := μ) hstat hdep
  calc
    FiniteDependence.MIS.Model.prob μ (cylStr (a := (0 : ℤ)) "0010100") =
        Poly3.eval (pVal μ) (tVal μ) 0 (certPoly cert_0010100) := h
    _ = Poly3.eval (pVal μ) (tVal μ) 0 poly_0010100 := by
          simpa [certPoly_0010100_eq]
    _ = (-2) * (pVal μ) ^ 2 + (-7) * pVal μ + 3 * tVal μ + 3 := by
          simp [poly_0010100, pPoly, tPoly, Poly3.eval_add, Poly3.eval_sub, Poly3.eval_mul, Poly3.eval_smul,
            Poly3.eval_pow, Poly3.eval_varP, Poly3.eval_varT, Poly3.eval_const]

private theorem prob_10100_eq_formula (μ : Measure FiniteDependence.MIS.State) [IsProbabilityMeasure μ]
    (hstat : Stationary μ) (hdep : KDependent 5 μ) :
    FiniteDependence.MIS.Model.prob μ (cylStr (a := (0 : ℤ)) "10100") =
      (-1) * (pVal μ) ^ 2 + (-2) * pVal μ + tVal μ + 1 := by
  have h := prob_10100_eq_eval (μ := μ) hstat hdep
  calc
    FiniteDependence.MIS.Model.prob μ (cylStr (a := (0 : ℤ)) "10100") =
        Poly3.eval (pVal μ) (tVal μ) 0 (certPoly cert_10100) := h
    _ = Poly3.eval (pVal μ) (tVal μ) 0 poly_10100 := by
          simpa [certPoly_10100_eq]
    _ = (-1) * (pVal μ) ^ 2 + (-2) * pVal μ + tVal μ + 1 := by
          simp [poly_10100, pPoly, tPoly, Poly3.eval_add, Poly3.eval_sub, Poly3.eval_mul, Poly3.eval_smul,
            Poly3.eval_pow, Poly3.eval_varP, Poly3.eval_varT, Poly3.eval_const]

private theorem prob_00100_eq_formula (μ : Measure FiniteDependence.MIS.State) [IsProbabilityMeasure μ]
    (hstat : Stationary μ) (hdep : KDependent 5 μ) :
    FiniteDependence.MIS.Model.prob μ (cylStr (a := (0 : ℤ)) "00100") =
      (pVal μ) ^ 2 - tVal μ := by
  have h := prob_00100_eq_eval (μ := μ) hstat hdep
  calc
    FiniteDependence.MIS.Model.prob μ (cylStr (a := (0 : ℤ)) "00100") =
        Poly3.eval (pVal μ) (tVal μ) 0 (certPoly cert_00100) := h
    _ = Poly3.eval (pVal μ) (tVal μ) 0 poly_00100 := by
          simpa [certPoly_00100_eq]
    _ = (pVal μ) ^ 2 - tVal μ := by
          simp [poly_00100, pPoly, tPoly, Poly3.eval_add, Poly3.eval_sub, Poly3.eval_mul, Poly3.eval_smul,
            Poly3.eval_pow, Poly3.eval_varP, Poly3.eval_varT, Poly3.eval_const]
          ring

private theorem prob_10100101_eq_formula (μ : Measure FiniteDependence.MIS.State) [IsProbabilityMeasure μ]
    (hstat : Stationary μ) (hdep : KDependent 5 μ) :
    FiniteDependence.MIS.Model.prob μ (cylStr (a := (0 : ℤ)) "10100101") =
      (-1) * (pVal μ) ^ 2 + (-10) * pVal μ + 4 * tVal μ + 4 := by
  have h := prob_10100101_eq_eval (μ := μ) hstat hdep
  calc
    FiniteDependence.MIS.Model.prob μ (cylStr (a := (0 : ℤ)) "10100101") =
        Poly3.eval (pVal μ) (tVal μ) 0 (certPoly cert_10100101) := h
    _ = Poly3.eval (pVal μ) (tVal μ) 0 poly_10100101 := by
          simpa [certPoly_10100101_eq]
    _ = (-1) * (pVal μ) ^ 2 + (-10) * pVal μ + 4 * tVal μ + 4 := by
          simp [poly_10100101, pPoly, tPoly, Poly3.eval_add, Poly3.eval_sub, Poly3.eval_mul, Poly3.eval_smul,
            Poly3.eval_pow, Poly3.eval_varP, Poly3.eval_varT, Poly3.eval_const]

private theorem prob_00_eq_formula (μ : Measure FiniteDependence.MIS.State) [IsProbabilityMeasure μ]
    (hstat : Stationary μ) (hdep : KDependent 5 μ) :
    FiniteDependence.MIS.Model.prob μ (cylStr (a := (0 : ℤ)) "00") = 1 - 2 * pVal μ := by
  have h := prob_00_eq_eval (μ := μ) hstat hdep
  calc
    FiniteDependence.MIS.Model.prob μ (cylStr (a := (0 : ℤ)) "00") =
        Poly3.eval (pVal μ) (tVal μ) 0 (certPoly cert_00) := h
    _ = Poly3.eval (pVal μ) (tVal μ) 0 poly_00 := by
          simpa [certPoly_00_eq]
    _ = 1 - 2 * pVal μ := by
          simp [poly_00, pPoly, tPoly, Poly3.eval_add, Poly3.eval_sub, Poly3.eval_mul, Poly3.eval_smul,
            Poly3.eval_pow, Poly3.eval_varP, Poly3.eval_varT, Poly3.eval_const]
          ring

theorem prob_101010010010100_eq_formula (μ : Measure FiniteDependence.MIS.State) [IsProbabilityMeasure μ]
    (hstat : Stationary μ) (hdep : KDependent 5 μ) :
    FiniteDependence.MIS.Model.prob μ (cylStr (a := (0 : ℤ)) "101010010010100") =
      (-1) * (pVal μ) ^ 4 + (-10) * (pVal μ) ^ 3 + 2 * (pVal μ) ^ 2 * tVal μ +
        (-37) * (pVal μ) ^ 2 + 19 * pVal μ * tVal μ + 34 * pVal μ -
        (tVal μ) ^ 2 + (-8) * tVal μ + (-7) := by
  have h101_mem : ("101" : String) ∈ K5Data.allowedWords 3 := by native_decide
  have h0010100_mem : ("0010100" : String) ∈ K5Data.allowedWords 7 := by native_decide
  have h10100_mem : ("10100" : String) ∈ K5Data.allowedWords 5 := by native_decide
  have h00100_mem : ("00100" : String) ∈ K5Data.allowedWords 5 := by native_decide
  have h10100101_mem : ("10100101" : String) ∈ K5Data.allowedWords 8 := by native_decide
  have h00_mem : ("00" : String) ∈ K5Data.allowedWords 2 := by native_decide

  have h101_01 : Is01String ("101" : String) := Is01String.of_mem_allowedWords (L := 3) h101_mem
  have h0010100_01 : Is01String ("0010100" : String) := Is01String.of_mem_allowedWords (L := 7) h0010100_mem
  have h10100_01 : Is01String ("10100" : String) := Is01String.of_mem_allowedWords (L := 5) h10100_mem
  have h00100_01 : Is01String ("00100" : String) := Is01String.of_mem_allowedWords (L := 5) h00100_mem
  have h10100101_01 : Is01String ("10100101" : String) := Is01String.of_mem_allowedWords (L := 8) h10100101_mem
  have h00_01 : Is01String ("00" : String) := Is01String.of_mem_allowedWords (L := 2) h00_mem

  have hrow1 :
      FiniteDependence.MIS.Model.prob μ (cylStr (a := (0 : ℤ)) "101") *
          FiniteDependence.MIS.Model.prob μ (cylStr (a := (0 : ℤ)) "0010100") =
        FiniteDependence.MIS.Model.prob μ (cylStr (a := (0 : ℤ)) "101001010010100") +
          FiniteDependence.MIS.Model.prob μ (cylStr (a := (0 : ℤ)) "101010010010100") := by
    have hsplit := prob_prod_gap5 (μ := μ) hstat hdep
      (m := 3) (n := 7) (x := ("101" : String)) (y := ("0010100" : String))
      h101_01 h0010100_01 (by native_decide) (by native_decide)
    have hS :
        (allowedWordsFinset (3 + 5 + 7)).filter
            (fun w => prefixOf w 3 = ("101" : String) ∧ suffixFrom w (3 + 5) = ("0010100" : String)) =
          ({("101001010010100" : String), "101010010010100"} : Finset String) := by
      native_decide
    simpa [hS, add_assoc, add_left_comm, add_comm] using hsplit

  have hrow2 :
      FiniteDependence.MIS.Model.prob μ (cylStr (a := (0 : ℤ)) "10100") *
          FiniteDependence.MIS.Model.prob μ (cylStr (a := (0 : ℤ)) "00100") =
        FiniteDependence.MIS.Model.prob μ (cylStr (a := (0 : ℤ)) "101001010100100") := by
    have hsplit := prob_prod_gap5 (μ := μ) hstat hdep
      (m := 5) (n := 5) (x := ("10100" : String)) (y := ("00100" : String))
      h10100_01 h00100_01 (by native_decide) (by native_decide)
    have hS :
        (allowedWordsFinset (5 + 5 + 5)).filter
            (fun w => prefixOf w 5 = ("10100" : String) ∧ suffixFrom w (5 + 5) = ("00100" : String)) =
          ({("101001010100100" : String)} : Finset String) := by
      native_decide
    simpa [hS] using hsplit

  have hrow3 :
      FiniteDependence.MIS.Model.prob μ (cylStr (a := (0 : ℤ)) "10100101") *
          FiniteDependence.MIS.Model.prob μ (cylStr (a := (0 : ℤ)) "00") =
        FiniteDependence.MIS.Model.prob μ (cylStr (a := (0 : ℤ)) "101001010010100") +
          FiniteDependence.MIS.Model.prob μ (cylStr (a := (0 : ℤ)) "101001010100100") := by
    have hsplit := prob_prod_gap5 (μ := μ) hstat hdep
      (m := 8) (n := 2) (x := ("10100101" : String)) (y := ("00" : String))
      h10100101_01 h00_01 (by native_decide) (by native_decide)
    have hS :
        (allowedWordsFinset (8 + 5 + 2)).filter
            (fun w => prefixOf w 8 = ("10100101" : String) ∧ suffixFrom w (8 + 5) = ("00" : String)) =
          ({("101001010010100" : String), "101001010100100"} : Finset String) := by
      native_decide
    simpa [hS, add_assoc, add_left_comm, add_comm] using hsplit

  have hmain :
      FiniteDependence.MIS.Model.prob μ (cylStr (a := (0 : ℤ)) "101010010010100") =
        FiniteDependence.MIS.Model.prob μ (cylStr (a := (0 : ℤ)) "101") *
            FiniteDependence.MIS.Model.prob μ (cylStr (a := (0 : ℤ)) "0010100") +
          FiniteDependence.MIS.Model.prob μ (cylStr (a := (0 : ℤ)) "10100") *
            FiniteDependence.MIS.Model.prob μ (cylStr (a := (0 : ℤ)) "00100") -
          FiniteDependence.MIS.Model.prob μ (cylStr (a := (0 : ℤ)) "10100101") *
            FiniteDependence.MIS.Model.prob μ (cylStr (a := (0 : ℤ)) "00") := by
    linarith [hrow1, hrow2, hrow3]

  have h101 := prob_101_eq_formula (μ := μ) hstat hdep
  have h0010100 := prob_0010100_eq_formula (μ := μ) hstat hdep
  have h10100 := prob_10100_eq_formula (μ := μ) hstat hdep
  have h00100 := prob_00100_eq_formula (μ := μ) hstat hdep
  have h10100101 := prob_10100101_eq_formula (μ := μ) hstat hdep
  have h00 := prob_00_eq_formula (μ := μ) hstat hdep

  have hpoly :
      FiniteDependence.MIS.Model.prob μ (cylStr (a := (0 : ℤ)) "101010010010100") =
        (-1) * (pVal μ) ^ 4 + (-10) * (pVal μ) ^ 3 + 2 * (pVal μ) ^ 2 * tVal μ +
          (-37) * (pVal μ) ^ 2 + 19 * pVal μ * tVal μ + 34 * pVal μ -
          (tVal μ) ^ 2 + (-8) * tVal μ + (-7) := by
    have hmain' := hmain
    simp_rw [h101, h0010100, h10100, h00100, h10100101, h00] at hmain'
    ring_nf at hmain'
    convert hmain' using 1 <;> ring_nf
  simpa using hpoly

end Step4Sparse

end

end Model

end K5Bridge

end FiniteDependence.MIS
