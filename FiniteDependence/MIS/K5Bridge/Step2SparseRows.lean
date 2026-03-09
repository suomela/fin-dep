import FiniteDependence.MIS.K5Bridge.Step2SparseFilters1
import FiniteDependence.MIS.K5Bridge.Step2SparseFilters2
import FiniteDependence.MIS.K5Bridge.Step2SparseFilters3
import FiniteDependence.MIS.K5Bridge.Step2SparseFilters4

set_option maxRecDepth 1000000
set_option maxHeartbeats 20000000

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

private lemma mem_allowedWords_of_finset {L : Nat} {s : String} (hs : s ∈ allowedWordsFinset L) :
    s ∈ K5Data.allowedWords L :=
  (mem_allowedWordsFinset_iff (L := L) (s := s)).1 hs

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

set_option maxHeartbeats 20000000 in
set_option maxRecDepth 1000000 in
theorem f_row_combination_zero (μ : Measure FiniteDependence.MIS.State) [IsProbabilityMeasure μ]
    (hstat : Stationary μ) (hdep : KDependent 5 μ) :
    let P : String → ℝ := fun s => FiniteDependence.MIS.Model.prob μ (cylStr (a := (0 : ℤ)) s)
    P "1" * P "0010100101" - P "100" * P "10100101" +
      P "10100" * P "001001" - P "10100" * P "100101" +
      P "100100" * P "00101" + P "10100101" * P "101" -
      P "1010010101" * P "1" = 0 := by
  let P : String → ℝ := fun s => FiniteDependence.MIS.Model.prob μ (cylStr (a := (0 : ℤ)) s)
  have h1_mem : ("1" : String) ∈ K5Data.allowedWords 1 :=
    mem_allowedWords_of_finset (by decide : ("1" : String) ∈ allowedWordsFinset 1)
  have h0010100101_mem : ("0010100101" : String) ∈ K5Data.allowedWords 10 :=
    mem_allowedWords_of_finset (by decide : ("0010100101" : String) ∈ allowedWordsFinset 10)
  have h100_mem : ("100" : String) ∈ K5Data.allowedWords 3 :=
    mem_allowedWords_of_finset (by decide : ("100" : String) ∈ allowedWordsFinset 3)
  have h10100101_mem : ("10100101" : String) ∈ K5Data.allowedWords 8 :=
    mem_allowedWords_of_finset (by decide : ("10100101" : String) ∈ allowedWordsFinset 8)
  have h10100_mem : ("10100" : String) ∈ K5Data.allowedWords 5 :=
    mem_allowedWords_of_finset (by decide : ("10100" : String) ∈ allowedWordsFinset 5)
  have h001001_mem : ("001001" : String) ∈ K5Data.allowedWords 6 :=
    mem_allowedWords_of_finset (by decide : ("001001" : String) ∈ allowedWordsFinset 6)
  have h100101_mem : ("100101" : String) ∈ K5Data.allowedWords 6 :=
    mem_allowedWords_of_finset (by decide : ("100101" : String) ∈ allowedWordsFinset 6)
  have h100100_mem : ("100100" : String) ∈ K5Data.allowedWords 6 :=
    mem_allowedWords_of_finset (by decide : ("100100" : String) ∈ allowedWordsFinset 6)
  have h00101_mem : ("00101" : String) ∈ K5Data.allowedWords 5 :=
    mem_allowedWords_of_finset (by decide : ("00101" : String) ∈ allowedWordsFinset 5)
  have h101_mem : ("101" : String) ∈ K5Data.allowedWords 3 :=
    mem_allowedWords_of_finset (by decide : ("101" : String) ∈ allowedWordsFinset 3)
  have h1010010101_mem : ("1010010101" : String) ∈ K5Data.allowedWords 10 :=
    mem_allowedWords_of_finset (by decide : ("1010010101" : String) ∈ allowedWordsFinset 10)

  have h1sum :=
    prob_prod_gap5_sum (μ := μ) hstat hdep
      (hx := h1_mem)
      (hy := h0010100101_mem)
  have hS1 := filter_1_0010100101_eq
  have h1 :
      P "1" * P "0010100101" =
        P "1001010010100101" + P "1010010010100101" := by
    simpa [P, hS1, add_assoc, add_left_comm, add_comm] using h1sum

  have h2sum :=
    prob_prod_gap5_sum (μ := μ) hstat hdep
      (hx := h100_mem)
      (hy := h10100101_mem)
  have hS2 := filter_100_10100101_eq
  have h2 :
      P "100" * P "10100101" =
        P "1001001010100101" + P "1001010010100101" := by
    simpa [P, hS2, add_assoc, add_left_comm, add_comm] using h2sum

  have h3sum :=
    prob_prod_gap5_sum (μ := μ) hstat hdep
      (hx := h10100_mem)
      (hy := h001001_mem)
  have hS3 := filter_10100_001001_eq
  have h3 :
      P "10100" * P "001001" = P "1010010101001001" := by
    simpa [P, hS3] using h3sum

  have h4sum :=
    prob_prod_gap5_sum (μ := μ) hstat hdep
      (hx := h10100_mem)
      (hy := h100101_mem)
  have hS4 := filter_10100_100101_eq
  have h4 :
      P "10100" * P "100101" =
        P "1010010010100101" + P "1010010100100101" := by
    simpa [P, hS4, add_assoc, add_left_comm, add_comm] using h4sum

  have h5sum :=
    prob_prod_gap5_sum (μ := μ) hstat hdep
      (hx := h100100_mem)
      (hy := h00101_mem)
  have hS5 := filter_100100_00101_eq
  have h5 :
      P "100100" * P "00101" = P "1001001010100101" := by
    simpa [P, hS5] using h5sum

  have h6sum :=
    prob_prod_gap5_sum (μ := μ) hstat hdep
      (hx := h10100101_mem)
      (hy := h101_mem)
  have hS6 := filter_10100101_101_eq
  have h6 :
      P "10100101" * P "101" =
        P "1010010100100101" + P "1010010101010101" := by
    simpa [P, hS6, add_assoc, add_left_comm, add_comm] using h6sum

  have h7sum :=
    prob_prod_gap5_sum (μ := μ) hstat hdep
      (hx := h1010010101_mem)
      (hy := h1_mem)
  have hS7 := filter_1010010101_1_eq
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

set_option maxHeartbeats 20000000 in
set_option maxRecDepth 1000000 in
theorem r_row_combination_zero (μ : Measure FiniteDependence.MIS.State) [IsProbabilityMeasure μ]
    (hstat : Stationary μ) (hdep : KDependent 5 μ) :
    let P : String → ℝ := fun s => FiniteDependence.MIS.Model.prob μ (cylStr (a := (0 : ℤ)) s)
    (-(P "00100" * P "1010010100") + P "00100100" * P "0010100" +
      P "0010010100" * P "10100" - P "0010010100100" * P "00") = 0 := by
  let P : String → ℝ := fun s => FiniteDependence.MIS.Model.prob μ (cylStr (a := (0 : ℤ)) s)
  have h00100_mem : ("00100" : String) ∈ K5Data.allowedWords 5 :=
    mem_allowedWords_of_finset (by decide : ("00100" : String) ∈ allowedWordsFinset 5)
  have h1010010100_mem : ("1010010100" : String) ∈ K5Data.allowedWords 10 :=
    mem_allowedWords_of_finset (by decide : ("1010010100" : String) ∈ allowedWordsFinset 10)
  have h00100100_mem : ("00100100" : String) ∈ K5Data.allowedWords 8 :=
    mem_allowedWords_of_finset (by decide : ("00100100" : String) ∈ allowedWordsFinset 8)
  have h0010100_mem : ("0010100" : String) ∈ K5Data.allowedWords 7 :=
    mem_allowedWords_of_finset (by decide : ("0010100" : String) ∈ allowedWordsFinset 7)
  have h0010010100_mem : ("0010010100" : String) ∈ K5Data.allowedWords 10 :=
    mem_allowedWords_of_finset (by decide : ("0010010100" : String) ∈ allowedWordsFinset 10)
  have h10100_mem : ("10100" : String) ∈ K5Data.allowedWords 5 :=
    mem_allowedWords_of_finset (by decide : ("10100" : String) ∈ allowedWordsFinset 5)
  have h0010010100100_mem : ("0010010100100" : String) ∈ K5Data.allowedWords 13 :=
    mem_allowedWords_of_finset (by decide : ("0010010100100" : String) ∈ allowedWordsFinset 13)
  have h00_mem : ("00" : String) ∈ K5Data.allowedWords 2 :=
    mem_allowedWords_of_finset (by decide : ("00" : String) ∈ allowedWordsFinset 2)

  have h1sum :=
    prob_prod_gap5_sum (μ := μ) hstat hdep
      (hx := h00100_mem)
      (hy := h1010010100_mem)
  have hS1 := filter_00100_1010010100_eq
  have h1 :
      P "00100" * P "1010010100" =
        P "00100100101010010100" + P "00100101001010010100" := by
    simpa [P, hS1, add_assoc, add_left_comm, add_comm] using h1sum

  have h2sum :=
    prob_prod_gap5_sum (μ := μ) hstat hdep
      (hx := h00100100_mem)
      (hy := h0010100_mem)
  have hS2 := filter_00100100_0010100_eq
  have h2 :
      P "00100100" * P "0010100" = P "00100100101010010100" := by
    simpa [P, hS2] using h2sum

  have h3sum :=
    prob_prod_gap5_sum (μ := μ) hstat hdep
      (hx := h0010010100_mem)
      (hy := h10100_mem)
  have hS3 := filter_0010010100_10100_eq
  have h3 :
      P "0010010100" * P "10100" =
        P "00100101001001010100" + P "00100101001010010100" := by
    simpa [P, hS3, add_assoc, add_left_comm, add_comm] using h3sum

  have h4sum :=
    prob_prod_gap5_sum (μ := μ) hstat hdep
      (hx := h0010010100100_mem)
      (hy := h00_mem)
  have hS4 := filter_0010010100100_00_eq
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
