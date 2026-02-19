import FiniteDependence.MIS.K5Bridge.Dist7
import FiniteDependence.MIS.K5Bridge.Length25Rows
import FiniteDependence.MIS.K5Bridge.Step4SparseWords

namespace FiniteDependence.MIS

namespace K5Bridge

open MeasureTheory Set
open scoped ProbabilityTheory

namespace Model

open FiniteDependence.MIS.Model

noncomputable section

namespace Step4Sparse

open Step3 Step2Sparse

/-- Step-4 compatibility polynomial from the length-19/25 sparse certificate. -/
def qCompat (p t : ℝ) : ℝ :=
  4 * p ^ 6 + 64 * p ^ 5 + (-12) * p ^ 4 * t + 528 * p ^ 4 + (-240) * p ^ 3 * t +
    80 * p ^ 3 + 12 * p ^ 2 * t ^ 2 + (-576) * p ^ 2 * t + (-552) * p ^ 2 +
    180 * p * t ^ 2 + 540 * p * t + 260 * p + (-4) * t ^ 3 + (-72) * t ^ 2 +
    (-108) * t + (-35)

private def qQuarter (p t : ℝ) : ℝ :=
  p ^ 6 + 16 * p ^ 5 + (-3) * p ^ 4 * t + 132 * p ^ 4 + (-60) * p ^ 3 * t +
    20 * p ^ 3 + 3 * p ^ 2 * t ^ 2 + (-144) * p ^ 2 * t + (-138) * p ^ 2 +
    45 * p * t ^ 2 + 135 * p * t + 65 * p + (-1) * t ^ 3 + (-18) * t ^ 2 +
    (-27) * t + ((-35 : ℝ) / 4)

private theorem dist7_selected_formulas (μ : Measure FiniteDependence.MIS.State) [IsProbabilityMeasure μ]
    (hstat : Stationary μ) (hdep : KDependent 5 μ) :
    FiniteDependence.MIS.Model.prob μ (cylStr (a := (0 : ℤ)) "0010010") = (pVal μ) ^ 2 - tVal μ ∧
      FiniteDependence.MIS.Model.prob μ (cylStr (a := (0 : ℤ)) "0010100") =
        (-(2 : ℝ)) * (pVal μ) ^ 2 + (-(7 : ℝ)) * pVal μ + 3 * tVal μ + 3 ∧
      FiniteDependence.MIS.Model.prob μ (cylStr (a := (0 : ℤ)) "0010101") =
        (pVal μ) ^ 2 + 5 * pVal μ - 2 * tVal μ - 2 ∧
      FiniteDependence.MIS.Model.prob μ (cylStr (a := (0 : ℤ)) "1010100") =
        (pVal μ) ^ 2 + 5 * pVal μ - 2 * tVal μ - 2 := by
  have hraw := (by simpa [pVal, tVal] using prob_dist7_formulas (μ := μ) hstat hdep)
  have h0010010 := hraw.1
  have h0010100 := hraw.2.1
  have h0010101 := hraw.2.2.1
  have h1010100 := hraw.2.2.2.2.2.2.2.2.2.2
  have h0010010' :
      FiniteDependence.MIS.Model.prob μ (cylStr (a := (0 : ℤ)) "0010010") = (pVal μ) ^ 2 - tVal μ := by
    simpa [pVal, tVal] using h0010010
  have h0010100' :
      FiniteDependence.MIS.Model.prob μ (cylStr (a := (0 : ℤ)) "0010100") =
        (-(2 : ℝ)) * (pVal μ) ^ 2 + (-(7 : ℝ)) * pVal μ + 3 * tVal μ + 3 := by
    have htmp :
        FiniteDependence.MIS.Model.prob μ (cylStr (a := (0 : ℤ)) "0010100") =
          -(2 * (pVal μ) ^ 2) + (-(7 : ℝ)) * pVal μ + 3 * tVal μ + 3 := by
      simpa [pVal, tVal] using h0010100
    have htmp' := htmp
    ring_nf at htmp'
    convert htmp' using 1 <;> ring_nf
  have h0010101' :
      FiniteDependence.MIS.Model.prob μ (cylStr (a := (0 : ℤ)) "0010101") =
        (pVal μ) ^ 2 + 5 * pVal μ - 2 * tVal μ - 2 := by
    simpa [pVal, tVal] using h0010101
  have h1010100' :
      FiniteDependence.MIS.Model.prob μ (cylStr (a := (0 : ℤ)) "1010100") =
        (pVal μ) ^ 2 + 5 * pVal μ - 2 * tVal μ - 2 := by
    simpa [pVal, tVal] using h1010100
  exact ⟨h0010010', h0010100', h0010101', h1010100'⟩

private theorem prob_00100_eq_formula (μ : Measure FiniteDependence.MIS.State) [IsProbabilityMeasure μ]
    (hstat : Stationary μ) (hdep : KDependent 5 μ) :
    FiniteDependence.MIS.Model.prob μ (cylStr (a := (0 : ℤ)) "00100") = (pVal μ) ^ 2 - tVal μ := by
  rcases dist7_selected_formulas (μ := μ) hstat hdep with ⟨h0010010, _h0010100, _h0010101, _h1010100⟩
  have hx_mem : ("00100" : String) ∈ K5Data.allowedWords 5 := by native_decide
  have hx01 : Is01String ("00100" : String) := Is01String.of_mem_allowedWords (L := 5) hx_mem
  have hxLen : ("00100" : String).length = 5 := by native_decide
  have hsum :
      FiniteDependence.MIS.Model.prob μ (cylStr (a := (0 : ℤ)) "00100") =
        ∑ w ∈ (allowedWordsFinset 7).filter (fun w => prefixOf w 5 = ("00100" : String)),
          FiniteDependence.MIS.Model.prob μ (cylStr (a := (0 : ℤ)) w) := by
    simpa using
      (prob_prefix_eq_sum (μ := μ) (a := (0 : ℤ)) (L := 7) (m := 5) (hL := by decide)
        (hm := by decide) (x := ("00100" : String)) hx01 hxLen)
  have hS :
      (allowedWordsFinset 7).filter (fun w => prefixOf w 5 = ("00100" : String)) =
        ({("0010010" : String)} : Finset String) := by
    native_decide
  calc
    FiniteDependence.MIS.Model.prob μ (cylStr (a := (0 : ℤ)) "00100") =
        FiniteDependence.MIS.Model.prob μ (cylStr (a := (0 : ℤ)) "0010010") := by
          simpa [hS] using hsum
    _ = (pVal μ) ^ 2 - tVal μ := h0010010

private theorem prob_0010100_eq_formula (μ : Measure FiniteDependence.MIS.State) [IsProbabilityMeasure μ]
    (hstat : Stationary μ) (hdep : KDependent 5 μ) :
    FiniteDependence.MIS.Model.prob μ (cylStr (a := (0 : ℤ)) "0010100") =
      (-(2 : ℝ)) * (pVal μ) ^ 2 + (-(7 : ℝ)) * pVal μ + 3 * tVal μ + 3 := by
  rcases dist7_selected_formulas (μ := μ) hstat hdep with ⟨_h0010010, h0010100, _h0010101, _h1010100⟩
  exact h0010100

private theorem prob_0010101_eq_formula (μ : Measure FiniteDependence.MIS.State) [IsProbabilityMeasure μ]
    (hstat : Stationary μ) (hdep : KDependent 5 μ) :
    FiniteDependence.MIS.Model.prob μ (cylStr (a := (0 : ℤ)) "0010101") =
      (pVal μ) ^ 2 + 5 * pVal μ - 2 * tVal μ - 2 := by
  rcases dist7_selected_formulas (μ := μ) hstat hdep with ⟨_h0010010, _h0010100, h0010101, _h1010100⟩
  exact h0010101

private theorem prob_00_eq_formula (μ : Measure FiniteDependence.MIS.State) [IsProbabilityMeasure μ]
    (hstat : Stationary μ) (hdep : KDependent 5 μ) :
    FiniteDependence.MIS.Model.prob μ (cylStr (a := (0 : ℤ)) "00") = 1 - 2 * pVal μ := by
  rcases dist7_selected_formulas (μ := μ) hstat hdep with
    ⟨h0010010, h0010100, h0010101, _h1010100⟩
  have hx_mem : ("00" : String) ∈ K5Data.allowedWords 2 := by native_decide
  have hx01 : Is01String ("00" : String) := Is01String.of_mem_allowedWords (L := 2) hx_mem
  have hxLen : ("00" : String).length = 2 := by native_decide
  have hsum :
      FiniteDependence.MIS.Model.prob μ (cylStr (a := (0 : ℤ)) "00") =
        ∑ w ∈ (allowedWordsFinset 7).filter (fun w => prefixOf w 2 = ("00" : String)),
          FiniteDependence.MIS.Model.prob μ (cylStr (a := (0 : ℤ)) w) := by
    simpa using
      (prob_prefix_eq_sum (μ := μ) (a := (0 : ℤ)) (L := 7) (m := 2) (hL := by decide)
        (hm := by decide) (x := ("00" : String)) hx01 hxLen)
  have hS :
      (allowedWordsFinset 7).filter (fun w => prefixOf w 2 = ("00" : String)) =
        ({("0010010" : String), "0010100", "0010101"} : Finset String) := by
    native_decide
  have hsum' :
      FiniteDependence.MIS.Model.prob μ (cylStr (a := (0 : ℤ)) "00") =
        FiniteDependence.MIS.Model.prob μ (cylStr (a := (0 : ℤ)) "0010010") +
          FiniteDependence.MIS.Model.prob μ (cylStr (a := (0 : ℤ)) "0010100") +
            FiniteDependence.MIS.Model.prob μ (cylStr (a := (0 : ℤ)) "0010101") := by
    simpa [hS, add_assoc, add_left_comm, add_comm] using hsum
  linarith [hsum', h0010010, h0010100, h0010101]

private theorem prob_01010100_eq_formula (μ : Measure FiniteDependence.MIS.State) [IsProbabilityMeasure μ]
    (hstat : Stationary μ) (hdep : KDependent 5 μ) :
    FiniteDependence.MIS.Model.prob μ (cylStr (a := (0 : ℤ)) "01010100") =
      (pVal μ) ^ 2 + 5 * pVal μ - 2 * tVal μ - 2 := by
  rcases dist7_selected_formulas (μ := μ) hstat hdep with
    ⟨_h0010010, _h0010100, _h0010101, h1010100⟩
  have hx_mem : ("1010100" : String) ∈ K5Data.allowedWords 7 := by native_decide
  have hx01 : Is01String ("1010100" : String) := Is01String.of_mem_allowedWords (L := 7) hx_mem
  have hxLen : ("1010100" : String).length = 7 := by native_decide
  have hsuf :
      FiniteDependence.MIS.Model.prob μ (cylStr (a := (1 : ℤ)) "1010100") =
        ∑ w ∈ (allowedWordsFinset 8).filter (fun w => suffix1 w = ("1010100" : String)),
          FiniteDependence.MIS.Model.prob μ (cylStr (a := (0 : ℤ)) w) := by
    simpa using
      (prob_suffix1_eq_sum (μ := μ) (a := (0 : ℤ)) (m := 7) (x := ("1010100" : String))
        hx01 hxLen)
  have hS :
      (allowedWordsFinset 8).filter (fun w => suffix1 w = ("1010100" : String)) =
        ({("01010100" : String)} : Finset String) := by
    native_decide
  have hsuf' :
      FiniteDependence.MIS.Model.prob μ (cylStr (a := (1 : ℤ)) "1010100") =
        FiniteDependence.MIS.Model.prob μ (cylStr (a := (0 : ℤ)) "01010100") := by
    simpa [hS] using hsuf
  have hshift :
      FiniteDependence.MIS.Model.prob μ (cylStr (a := (1 : ℤ)) "1010100") =
        FiniteDependence.MIS.Model.prob μ (cylStr (a := (0 : ℤ)) "1010100") := by
    simpa using
      (Stationary.prob_cylStr_succ (μ := μ) hstat (a := (0 : ℤ)) (s := ("1010100" : String)))
  linarith [hsuf', hshift, h1010100]

private def poly_0010010100 : Poly3.Poly :=
  ((2 : ℚ) • (pPoly ^ 2)) + ((-2 : ℚ) • pPoly) + (((1 : ℚ) / 2) • (1 : Poly3.Poly))

private theorem certPoly_0010010100_eq :
    certPoly cert_0010010100 = poly_0010010100 := by
  native_decide

private theorem prob_0010010100_eq_formula (μ : Measure FiniteDependence.MIS.State)
    [IsProbabilityMeasure μ] (hstat : Stationary μ) (hdep : KDependent 5 μ) :
    FiniteDependence.MIS.Model.prob μ (cylStr (a := (0 : ℤ)) "0010010100") =
      2 * (pVal μ) ^ 2 - 2 * pVal μ + (1 / 2 : ℝ) := by
  have hcert :
      FiniteDependence.MIS.Model.prob μ (cylStr (a := (0 : ℤ)) "0010010100") =
        Poly3.eval (pVal μ) (tVal μ) 0 (certPoly cert_0010010100) := by
    simpa using
      prob_prefix_eq_eval_certPoly (μ := μ) hstat hdep
        (m := 10) (x := "0010010100")
        (hx := by native_decide) (hm := by decide)
        (cert := cert_0010010100)
        (hmatch := cert_0010010100_matches)
  calc
    FiniteDependence.MIS.Model.prob μ (cylStr (a := (0 : ℤ)) "0010010100") =
        Poly3.eval (pVal μ) (tVal μ) 0 (certPoly cert_0010010100) := hcert
    _ = Poly3.eval (pVal μ) (tVal μ) 0 poly_0010010100 := by
          simpa [certPoly_0010010100_eq]
    _ = 2 * (pVal μ) ^ 2 - 2 * pVal μ + (1 / 2 : ℝ) := by
          simp [poly_0010010100, pPoly, tPoly, Poly3.eval_add, Poly3.eval_sub, Poly3.eval_mul,
            Poly3.eval_smul, Poly3.eval_pow, Poly3.eval_varP, Poly3.eval_varT, Poly3.eval_const]
          ring_nf

private theorem prob_suf19_eq_formula (μ : Measure FiniteDependence.MIS.State) [IsProbabilityMeasure μ]
    (hstat : Stationary μ) (hdep : KDependent 5 μ) :
    FiniteDependence.MIS.Model.prob μ (cylStr (a := (0 : ℤ)) "0010101010010010100") =
      FiniteDependence.MIS.Model.prob μ (cylStr (a := (0 : ℤ)) "0010101") *
          FiniteDependence.MIS.Model.prob μ (cylStr (a := (0 : ℤ)) "0010100") -
        FiniteDependence.MIS.Model.prob μ (cylStr (a := (0 : ℤ)) "00") *
          FiniteDependence.MIS.Model.prob μ (cylStr (a := (0 : ℤ)) "001010010100") := by
  have h00_mem : ("00" : String) ∈ K5Data.allowedWords 2 := by native_decide
  have h001010010100_mem : ("001010010100" : String) ∈ K5Data.allowedWords 12 := by native_decide
  have h0010101_mem : ("0010101" : String) ∈ K5Data.allowedWords 7 := by native_decide
  have h0010100_mem : ("0010100" : String) ∈ K5Data.allowedWords 7 := by native_decide
  have h00_01 : Is01String ("00" : String) := Is01String.of_mem_allowedWords (L := 2) h00_mem
  have h001010010100_01 : Is01String ("001010010100" : String) :=
    Is01String.of_mem_allowedWords (L := 12) h001010010100_mem
  have h0010101_01 : Is01String ("0010101" : String) := Is01String.of_mem_allowedWords (L := 7) h0010101_mem
  have h0010100_01 : Is01String ("0010100" : String) := Is01String.of_mem_allowedWords (L := 7) h0010100_mem

  have hrow_anchor :
      FiniteDependence.MIS.Model.prob μ (cylStr (a := (0 : ℤ)) "00") *
          FiniteDependence.MIS.Model.prob μ (cylStr (a := (0 : ℤ)) "001010010100") =
        FiniteDependence.MIS.Model.prob μ (cylStr (a := (0 : ℤ)) "0010101001010010100") := by
    have hsplit := prob_prod_gap5 (μ := μ) hstat hdep
      (m := 2) (n := 12) (x := ("00" : String)) (y := ("001010010100" : String))
      h00_01 h001010010100_01 (by native_decide) (by native_decide)
    have hS :
        (allowedWordsFinset (2 + 5 + 12)).filter
            (fun w => prefixOf w 2 = ("00" : String) ∧ suffixFrom w (2 + 5) = ("001010010100" : String)) =
          ({("0010101001010010100" : String)} : Finset String) := by
      native_decide
    simpa [hS] using hsplit

  have hrow_edge :
      FiniteDependence.MIS.Model.prob μ (cylStr (a := (0 : ℤ)) "0010101") *
          FiniteDependence.MIS.Model.prob μ (cylStr (a := (0 : ℤ)) "0010100") =
        FiniteDependence.MIS.Model.prob μ (cylStr (a := (0 : ℤ)) "0010101001010010100") +
          FiniteDependence.MIS.Model.prob μ (cylStr (a := (0 : ℤ)) "0010101010010010100") := by
    have hsplit := prob_prod_gap5 (μ := μ) hstat hdep
      (m := 7) (n := 7) (x := ("0010101" : String)) (y := ("0010100" : String))
      h0010101_01 h0010100_01 (by native_decide) (by native_decide)
    have hS :
        (allowedWordsFinset (7 + 5 + 7)).filter
            (fun w => prefixOf w 7 = ("0010101" : String) ∧ suffixFrom w (7 + 5) = ("0010100" : String)) =
          ({("0010101001010010100" : String), "0010101010010010100"} : Finset String) := by
      native_decide
    simpa [hS, add_assoc, add_left_comm, add_comm] using hsplit

  linarith [hrow_edge, hrow_anchor]

private theorem prob_s25_eq_formula (μ : Measure FiniteDependence.MIS.State) [IsProbabilityMeasure μ]
    (hstat : Stationary μ) (hdep : KDependent 5 μ) :
    FiniteDependence.MIS.Model.prob μ (cylStr (a := (0 : ℤ)) "0101010010101010010010100") =
      FiniteDependence.MIS.Model.prob μ (cylStr (a := (0 : ℤ)) "0101010010101") *
          FiniteDependence.MIS.Model.prob μ (cylStr (a := (0 : ℤ)) "0010100") -
        FiniteDependence.MIS.Model.prob μ (cylStr (a := (0 : ℤ)) "01010100") *
          FiniteDependence.MIS.Model.prob μ (cylStr (a := (0 : ℤ)) "001010010100") := by
  have h01010100_mem : ("01010100" : String) ∈ K5Data.allowedWords 8 := by native_decide
  have h001010010100_mem : ("001010010100" : String) ∈ K5Data.allowedWords 12 := by native_decide
  have h0101010010101_mem : ("0101010010101" : String) ∈ K5Data.allowedWords 13 := by native_decide
  have h0010100_mem : ("0010100" : String) ∈ K5Data.allowedWords 7 := by native_decide
  have h01010100_01 : Is01String ("01010100" : String) :=
    Is01String.of_mem_allowedWords (L := 8) h01010100_mem
  have h001010010100_01 : Is01String ("001010010100" : String) :=
    Is01String.of_mem_allowedWords (L := 12) h001010010100_mem
  have h0101010010101_01 : Is01String ("0101010010101" : String) :=
    Is01String.of_mem_allowedWords (L := 13) h0101010010101_mem
  have h0010100_01 : Is01String ("0010100" : String) := Is01String.of_mem_allowedWords (L := 7) h0010100_mem

  have hrow_anchor :
      FiniteDependence.MIS.Model.prob μ (cylStr (a := (0 : ℤ)) "01010100") *
          FiniteDependence.MIS.Model.prob μ (cylStr (a := (0 : ℤ)) "001010010100") =
        FiniteDependence.MIS.Model.prob μ (cylStr (a := (0 : ℤ)) "0101010010101001010010100") := by
    have hsplit := prob_prod_gap5 (μ := μ) hstat hdep
      (m := 8) (n := 12) (x := ("01010100" : String)) (y := ("001010010100" : String))
      h01010100_01 h001010010100_01 (by native_decide) (by native_decide)
    have hS :
        (allowedWordsFinset (8 + 5 + 12)).filter
            (fun w => prefixOf w 8 = ("01010100" : String) ∧ suffixFrom w (8 + 5) = ("001010010100" : String)) =
          ({("0101010010101001010010100" : String)} : Finset String) := by
      native_decide
    simpa [hS] using hsplit

  have hrow_edge :
      FiniteDependence.MIS.Model.prob μ (cylStr (a := (0 : ℤ)) "0101010010101") *
          FiniteDependence.MIS.Model.prob μ (cylStr (a := (0 : ℤ)) "0010100") =
        FiniteDependence.MIS.Model.prob μ (cylStr (a := (0 : ℤ)) "0101010010101001010010100") +
          FiniteDependence.MIS.Model.prob μ (cylStr (a := (0 : ℤ)) "0101010010101010010010100") := by
    have hsplit := prob_prod_gap5 (μ := μ) hstat hdep
      (m := 13) (n := 7) (x := ("0101010010101" : String)) (y := ("0010100" : String))
      h0101010010101_01 h0010100_01 (by native_decide) (by native_decide)
    have hS :
        (allowedWordsFinset (13 + 5 + 7)).filter
            (fun w => prefixOf w 13 = ("0101010010101" : String) ∧ suffixFrom w (13 + 5) = ("0010100" : String)) =
          ({("0101010010101001010010100" : String), "0101010010101010010010100"} : Finset String) := by
      native_decide
    simpa [hS, add_assoc, add_left_comm, add_comm] using hsplit

  linarith [hrow_edge, hrow_anchor]

theorem qCompat_eq_zero_prob (μ : Measure FiniteDependence.MIS.State) [IsProbabilityMeasure μ]
    (hstat : Stationary μ) (hdep : KDependent 5 μ) :
    qCompat (pVal μ) (tVal μ) = 0 := by
  have h0 : FiniteDependence.MIS.Model.prob μ (cylStr (a := (0 : ℤ)) "0") = 1 - pVal μ := by
    simpa [pVal] using (prob_cylStr0_0_eq_one_sub_prob1 (μ := μ))
  have h00100 := prob_00100_eq_formula (μ := μ) hstat hdep
  have h00 := prob_00_eq_formula (μ := μ) hstat hdep
  have h0010100 := prob_0010100_eq_formula (μ := μ) hstat hdep
  have h0010101 := prob_0010101_eq_formula (μ := μ) hstat hdep
  have h01010100 := prob_01010100_eq_formula (μ := μ) hstat hdep
  have h0010010100 := prob_0010010100_eq_formula (μ := μ) hstat hdep
  have h001010010100 := prob_001010010100_eq_formula (μ := μ) hstat hdep
  have h0101010010101 := prob_0101010010101_eq_formula (μ := μ) hstat hdep
  have h101010010010100 := prob_101010010010100_eq_formula (μ := μ) hstat hdep
  have hsuf19 := prob_suf19_eq_formula (μ := μ) hstat hdep
  have hs25 := prob_s25_eq_formula (μ := μ) hstat hdep
  have hsuf24 :
      FiniteDependence.MIS.Model.prob μ (cylStr (a := (0 : ℤ)) suf24) =
        FiniteDependence.MIS.Model.prob μ (cylStr (a := (0 : ℤ)) "0101010010101") *
            FiniteDependence.MIS.Model.prob μ (cylStr (a := (0 : ℤ)) "0010100") -
          FiniteDependence.MIS.Model.prob μ (cylStr (a := (0 : ℤ)) "01010100") *
            FiniteDependence.MIS.Model.prob μ (cylStr (a := (0 : ℤ)) "001010010100") := by
    calc
      FiniteDependence.MIS.Model.prob μ (cylStr (a := (0 : ℤ)) suf24) =
          FiniteDependence.MIS.Model.prob μ (cylStr (a := (0 : ℤ)) wB) := by
            simpa using (prob_row2736 (μ := μ) hstat).symm
      _ = FiniteDependence.MIS.Model.prob μ (cylStr (a := (0 : ℤ)) "0101010010101010010010100") := by
            simp [wB]
      _ = FiniteDependence.MIS.Model.prob μ (cylStr (a := (0 : ℤ)) "0101010010101") *
            FiniteDependence.MIS.Model.prob μ (cylStr (a := (0 : ℤ)) "0010100") -
          FiniteDependence.MIS.Model.prob μ (cylStr (a := (0 : ℤ)) "01010100") *
            FiniteDependence.MIS.Model.prob μ (cylStr (a := (0 : ℤ)) "001010010100") := hs25

  have hquarter :
      qQuarter (pVal μ) (tVal μ) = 0 := by
    have hcomb :
        (FiniteDependence.MIS.Model.prob μ (cylStr (a := (0 : ℤ)) "0") *
              FiniteDependence.MIS.Model.prob μ (cylStr (a := (0 : ℤ)) "0010101010010010100")) +
            (FiniteDependence.MIS.Model.prob μ (cylStr (a := (0 : ℤ)) "0010010100")) ^ 2 -
            FiniteDependence.MIS.Model.prob μ (cylStr (a := (0 : ℤ)) suf24) -
            (FiniteDependence.MIS.Model.prob μ (cylStr (a := (0 : ℤ)) "00100") *
              FiniteDependence.MIS.Model.prob μ (cylStr (a := (0 : ℤ)) "101010010010100")) = 0 := by
      simpa [suf19, mid10, suf15] using (rhs_combination_eq_zero (μ := μ) hstat hdep)
    rw [h0, hsuf19, h00, h0010010100, hsuf24, h00100, h101010010010100] at hcomb
    rw [h0010101, h0010100, h0101010010101, h01010100, h001010010100] at hcomb
    ring_nf at hcomb
    have hEq :
        -35 / 4 + pVal μ * 65 + pVal μ * tVal μ * 135 + pVal μ * tVal μ ^ 2 * 45 +
                (-(pVal μ ^ 2 * 138) - pVal μ ^ 2 * tVal μ * 144) +
              pVal μ ^ 2 * tVal μ ^ 2 * 3 +
            (pVal μ ^ 3 * 20 - pVal μ ^ 3 * tVal μ * 60) +
          (pVal μ ^ 4 * 132 - pVal μ ^ 4 * tVal μ * 3) +
        pVal μ ^ 5 * 16 +
      (pVal μ ^ 6 - tVal μ * 27) +
      (-(tVal μ ^ 2 * 18) - tVal μ ^ 3) =
      qQuarter (pVal μ) (tVal μ) := by
      simp [qQuarter]
      ring_nf
    linarith [hcomb, hEq]

  have hq : qCompat (pVal μ) (tVal μ) = 0 := by
    have hq4 : qCompat (pVal μ) (tVal μ) = 4 * qQuarter (pVal μ) (tVal μ) := by
      simp [qCompat, qQuarter]
      ring
    calc
      qCompat (pVal μ) (tVal μ) = 4 * qQuarter (pVal μ) (tVal μ) := hq4
      _ = 0 := by simp [hquarter]
  exact hq

end Step4Sparse

end

end Model

end K5Bridge

end FiniteDependence.MIS
