import FiniteDependence.MIS.K5Bridge.StepLemmas

namespace FiniteDependence.MIS

namespace K5Bridge

open MeasureTheory Set
open scoped ProbabilityTheory

namespace Model

open FiniteDependence.MIS.Model

noncomputable section

namespace Step2Sparse

private lemma is01_of_mem_allowedWords {L : Nat} {s : String} (hs : s ∈ K5Data.allowedWords L) :
    Is01String s :=
  Is01String.of_mem_allowedWords (L := L) (s := s) hs

private lemma prob_prod_gap5_sum (μ : Measure FiniteDependence.MIS.State) [IsProbabilityMeasure μ]
    (hstat : Stationary μ) (hdep : KDependent 5 μ)
    {m n : Nat} {x y : String}
    (hx : x ∈ K5Data.allowedWords m) (hy : y ∈ K5Data.allowedWords n) :
    FiniteDependence.MIS.Model.prob μ (cylStr (a := (0 : ℤ)) x) *
        FiniteDependence.MIS.Model.prob μ (cylStr (a := (0 : ℤ)) y) =
      ∑ w ∈ (allowedWordsFinset (m + 5 + n)).filter (fun w => prefixOf w m = x ∧ suffixFrom w (m + 5) = y),
        FiniteDependence.MIS.Model.prob μ (cylStr (a := (0 : ℤ)) w) := by
  have hx01 : Is01String x := is01_of_mem_allowedWords hx
  have hy01 : Is01String y := is01_of_mem_allowedWords hy
  have hxLen : x.length = m := length_of_mem_allowedWords (L := m) (s := x) hx
  have hyLen : y.length = n := length_of_mem_allowedWords (L := n) (s := y) hy
  exact prob_prod_gap5 (μ := μ) hstat hdep (m := m) (n := n) (x := x) (y := y) hx01 hy01 hxLen hyLen

theorem f_row_combination_zero (μ : Measure FiniteDependence.MIS.State) [IsProbabilityMeasure μ]
    (hstat : Stationary μ) (hdep : KDependent 5 μ) :
    let P : String → ℝ := fun s => FiniteDependence.MIS.Model.prob μ (cylStr (a := (0 : ℤ)) s)
    P "1" * P "0010100101" - P "100" * P "10100101" +
      P "10100" * P "001001" - P "10100" * P "100101" +
      P "100100" * P "00101" + P "10100101" * P "101" -
      P "1010010101" * P "1" = 0 := by
  let P : String → ℝ := fun s => FiniteDependence.MIS.Model.prob μ (cylStr (a := (0 : ℤ)) s)

  have h1sum :=
    prob_prod_gap5_sum (μ := μ) hstat hdep
      (hx := (by native_decide : ("1" : String) ∈ K5Data.allowedWords 1))
      (hy := (by native_decide : ("0010100101" : String) ∈ K5Data.allowedWords 10))
  have hS1 :
      (allowedWordsFinset (1 + 5 + 10)).filter
          (fun w => prefixOf w 1 = ("1" : String) ∧ suffixFrom w (1 + 5) = ("0010100101" : String)) =
        ({("1001010010100101" : String), "1010010010100101"} : Finset String) := by
    native_decide
  have h1 :
      P "1" * P "0010100101" =
        P "1001010010100101" + P "1010010010100101" := by
    simpa [P, hS1, add_assoc, add_left_comm, add_comm] using h1sum

  have h2sum :=
    prob_prod_gap5_sum (μ := μ) hstat hdep
      (hx := (by native_decide : ("100" : String) ∈ K5Data.allowedWords 3))
      (hy := (by native_decide : ("10100101" : String) ∈ K5Data.allowedWords 8))
  have hS2 :
      (allowedWordsFinset (3 + 5 + 8)).filter
          (fun w => prefixOf w 3 = ("100" : String) ∧ suffixFrom w (3 + 5) = ("10100101" : String)) =
        ({("1001001010100101" : String), "1001010010100101"} : Finset String) := by
    native_decide
  have h2 :
      P "100" * P "10100101" =
        P "1001001010100101" + P "1001010010100101" := by
    simpa [P, hS2, add_assoc, add_left_comm, add_comm] using h2sum

  have h3sum :=
    prob_prod_gap5_sum (μ := μ) hstat hdep
      (hx := (by native_decide : ("10100" : String) ∈ K5Data.allowedWords 5))
      (hy := (by native_decide : ("001001" : String) ∈ K5Data.allowedWords 6))
  have hS3 :
      (allowedWordsFinset (5 + 5 + 6)).filter
          (fun w => prefixOf w 5 = ("10100" : String) ∧ suffixFrom w (5 + 5) = ("001001" : String)) =
        ({("1010010101001001" : String)} : Finset String) := by
    native_decide
  have h3 :
      P "10100" * P "001001" = P "1010010101001001" := by
    simpa [P, hS3] using h3sum

  have h4sum :=
    prob_prod_gap5_sum (μ := μ) hstat hdep
      (hx := (by native_decide : ("10100" : String) ∈ K5Data.allowedWords 5))
      (hy := (by native_decide : ("100101" : String) ∈ K5Data.allowedWords 6))
  have hS4 :
      (allowedWordsFinset (5 + 5 + 6)).filter
          (fun w => prefixOf w 5 = ("10100" : String) ∧ suffixFrom w (5 + 5) = ("100101" : String)) =
        ({("1010010010100101" : String), "1010010100100101"} : Finset String) := by
    native_decide
  have h4 :
      P "10100" * P "100101" =
        P "1010010010100101" + P "1010010100100101" := by
    simpa [P, hS4, add_assoc, add_left_comm, add_comm] using h4sum

  have h5sum :=
    prob_prod_gap5_sum (μ := μ) hstat hdep
      (hx := (by native_decide : ("100100" : String) ∈ K5Data.allowedWords 6))
      (hy := (by native_decide : ("00101" : String) ∈ K5Data.allowedWords 5))
  have hS5 :
      (allowedWordsFinset (6 + 5 + 5)).filter
          (fun w => prefixOf w 6 = ("100100" : String) ∧ suffixFrom w (6 + 5) = ("00101" : String)) =
        ({("1001001010100101" : String)} : Finset String) := by
    native_decide
  have h5 :
      P "100100" * P "00101" = P "1001001010100101" := by
    simpa [P, hS5] using h5sum

  have h6sum :=
    prob_prod_gap5_sum (μ := μ) hstat hdep
      (hx := (by native_decide : ("10100101" : String) ∈ K5Data.allowedWords 8))
      (hy := (by native_decide : ("101" : String) ∈ K5Data.allowedWords 3))
  have hS6 :
      (allowedWordsFinset (8 + 5 + 3)).filter
          (fun w => prefixOf w 8 = ("10100101" : String) ∧ suffixFrom w (8 + 5) = ("101" : String)) =
        ({("1010010100100101" : String), "1010010101010101"} : Finset String) := by
    native_decide
  have h6 :
      P "10100101" * P "101" =
        P "1010010100100101" + P "1010010101010101" := by
    simpa [P, hS6, add_assoc, add_left_comm, add_comm] using h6sum

  have h7sum :=
    prob_prod_gap5_sum (μ := μ) hstat hdep
      (hx := (by native_decide : ("1010010101" : String) ∈ K5Data.allowedWords 10))
      (hy := (by native_decide : ("1" : String) ∈ K5Data.allowedWords 1))
  have hS7 :
      (allowedWordsFinset (10 + 5 + 1)).filter
          (fun w => prefixOf w 10 = ("1010010101" : String) ∧ suffixFrom w (10 + 5) = ("1" : String)) =
        ({("1010010101001001" : String), "1010010101010101"} : Finset String) := by
    native_decide
  have h7 :
      P "1010010101" * P "1" =
        P "1010010101001001" + P "1010010101010101" := by
    simpa [P, hS7, add_assoc, add_left_comm, add_comm] using h7sum

  have htarget :
      P "1" * P "0010100101" - P "100" * P "10100101" +
        P "10100" * P "001001" - P "10100" * P "100101" +
        P "100100" * P "00101" + P "10100101" * P "101" -
        P "1010010101" * P "1" = 0 := by
    rw [h1, h2, h3, h4, h5, h6, h7]
    ring
  simpa [P] using htarget

theorem r_row_combination_zero (μ : Measure FiniteDependence.MIS.State) [IsProbabilityMeasure μ]
    (hstat : Stationary μ) (hdep : KDependent 5 μ) :
    let P : String → ℝ := fun s => FiniteDependence.MIS.Model.prob μ (cylStr (a := (0 : ℤ)) s)
    (-(P "00100" * P "1010010100") + P "00100100" * P "0010100" +
      P "0010010100" * P "10100" - P "0010010100100" * P "00") = 0 := by
  let P : String → ℝ := fun s => FiniteDependence.MIS.Model.prob μ (cylStr (a := (0 : ℤ)) s)

  have h1sum :=
    prob_prod_gap5_sum (μ := μ) hstat hdep
      (hx := (by native_decide : ("00100" : String) ∈ K5Data.allowedWords 5))
      (hy := (by native_decide : ("1010010100" : String) ∈ K5Data.allowedWords 10))
  have hS1 :
      (allowedWordsFinset (5 + 5 + 10)).filter
          (fun w => prefixOf w 5 = ("00100" : String) ∧ suffixFrom w (5 + 5) = ("1010010100" : String)) =
        ({("00100100101010010100" : String), "00100101001010010100"} : Finset String) := by
    native_decide
  have h1 :
      P "00100" * P "1010010100" =
        P "00100100101010010100" + P "00100101001010010100" := by
    simpa [P, hS1, add_assoc, add_left_comm, add_comm] using h1sum

  have h2sum :=
    prob_prod_gap5_sum (μ := μ) hstat hdep
      (hx := (by native_decide : ("00100100" : String) ∈ K5Data.allowedWords 8))
      (hy := (by native_decide : ("0010100" : String) ∈ K5Data.allowedWords 7))
  have hS2 :
      (allowedWordsFinset (8 + 5 + 7)).filter
          (fun w => prefixOf w 8 = ("00100100" : String) ∧ suffixFrom w (8 + 5) = ("0010100" : String)) =
        ({("00100100101010010100" : String)} : Finset String) := by
    native_decide
  have h2 :
      P "00100100" * P "0010100" = P "00100100101010010100" := by
    simpa [P, hS2] using h2sum

  have h3sum :=
    prob_prod_gap5_sum (μ := μ) hstat hdep
      (hx := (by native_decide : ("0010010100" : String) ∈ K5Data.allowedWords 10))
      (hy := (by native_decide : ("10100" : String) ∈ K5Data.allowedWords 5))
  have hS3 :
      (allowedWordsFinset (10 + 5 + 5)).filter
          (fun w => prefixOf w 10 = ("0010010100" : String) ∧ suffixFrom w (10 + 5) = ("10100" : String)) =
        ({("00100101001001010100" : String), "00100101001010010100"} : Finset String) := by
    native_decide
  have h3 :
      P "0010010100" * P "10100" =
        P "00100101001001010100" + P "00100101001010010100" := by
    simpa [P, hS3, add_assoc, add_left_comm, add_comm] using h3sum

  have h4sum :=
    prob_prod_gap5_sum (μ := μ) hstat hdep
      (hx := (by native_decide : ("0010010100100" : String) ∈ K5Data.allowedWords 13))
      (hy := (by native_decide : ("00" : String) ∈ K5Data.allowedWords 2))
  have hS4 :
      (allowedWordsFinset (13 + 5 + 2)).filter
          (fun w => prefixOf w 13 = ("0010010100100" : String) ∧ suffixFrom w (13 + 5) = ("00" : String)) =
        ({("00100101001001010100" : String)} : Finset String) := by
    native_decide
  have h4 :
      P "0010010100100" * P "00" = P "00100101001001010100" := by
    simpa [P, hS4] using h4sum

  have htarget :
      (-(P "00100" * P "1010010100") + P "00100100" * P "0010100" +
        P "0010010100" * P "10100" - P "0010010100100" * P "00") = 0 := by
    rw [h1, h2, h3, h4]
    ring
  simpa [P] using htarget

end Step2Sparse

end

end Model

end K5Bridge

end FiniteDependence.MIS
