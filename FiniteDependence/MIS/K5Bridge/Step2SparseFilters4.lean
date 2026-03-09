import FiniteDependence.MIS.K5Bridge.Step2SparseFiltersCore

namespace FiniteDependence.MIS

namespace K5Bridge

namespace Model

namespace Step2Sparse

theorem filter_0010010100_10100_eq :
    (allowedWordsFinset (10 + 5 + 5)).filter
        (fun w => prefixOf w 10 = ("0010010100" : String) ∧ suffixFrom w (10 + 5) = ("10100" : String)) =
      ({("00100101001001010100" : String), "00100101001010010100"} : Finset String) := by
  have h10_mem : ("0010010100" : String) ∈ allowedWordsFinset 10 := by decide
  have h10 :
      (allowedWordsFinset 10).filter (fun w => prefixOf w 10 = ("0010010100" : String)) =
        ({("0010010100" : String)} : Finset String) :=
    filter_prefix_exact h10_mem
  have h11 :
      (allowedWordsFinset 11).filter (fun w => prefixOf w 10 = ("0010010100" : String)) =
        ({("00100101001" : String)} : Finset String) := by
    rw [filter_prefix_step (m := 10) (n := 9) (x := ("0010010100" : String)) (by decide), h10]
    decide
  have h12 :
      (allowedWordsFinset 12).filter (fun w => prefixOf w 10 = ("0010010100" : String)) =
        ({("001001010010" : String)} : Finset String) := by
    rw [filter_prefix_step (m := 10) (n := 10) (x := ("0010010100" : String)) (by decide), h11]
    decide
  have h13 :
      (allowedWordsFinset 13).filter (fun w => prefixOf w 10 = ("0010010100" : String)) =
        ({("0010010100100" : String), "0010010100101"} : Finset String) := by
    rw [filter_prefix_step (m := 10) (n := 11) (x := ("0010010100" : String)) (by decide), h12]
    decide
  have h14 :
      (allowedWordsFinset 14).filter (fun w => prefixOf w 10 = ("0010010100" : String)) =
        ({("00100101001001" : String), "00100101001010"} : Finset String) := by
    rw [filter_prefix_step (m := 10) (n := 12) (x := ("0010010100" : String)) (by decide), h13]
    decide
  have h15 :
      (allowedWordsFinset 15).filter (fun w => prefixOf w 10 = ("0010010100" : String)) =
        ({("001001010010010" : String), "001001010010100", "001001010010101"} : Finset String) := by
    rw [filter_prefix_step (m := 10) (n := 13) (x := ("0010010100" : String)) (by decide), h14]
    decide
  have h15_empty :
      (allowedWordsFinset 15).filter
          (fun w => prefixOf w 10 = ("0010010100" : String) ∧ suffixFrom w 15 = ("" : String)) =
        ({("001001010010010" : String), "001001010010100", "001001010010101"} : Finset String) := by
    rw [filter_pref_suf_empty (m := 10) (L := 15) (x := ("0010010100" : String)) (by decide), h15]
  have h16 :
      (allowedWordsFinset 16).filter
          (fun w => prefixOf w 10 = ("0010010100" : String) ∧ suffixFrom w 15 = ("1" : String)) =
        ({("0010010100100101" : String), "0010010100101001"} : Finset String) := by
    rw [show
      (allowedWordsFinset 16).filter
          (fun w => prefixOf w 10 = ("0010010100" : String) ∧ suffixFrom w 15 = ("1" : String)) =
        (((allowedWordsFinset 15).filter
            (fun w => prefixOf w 10 = ("0010010100" : String) ∧ suffixFrom w 15 = ("" : String))).biUnion
          fun w => ((K5Data.extensions w).toFinset).filter
            (fun s => suffixFrom s 15 = ("1" : String))) from by
          simpa using
            (filter_pref_suf_step (m := 10) (n := 14) (x := ("0010010100" : String)) (u := ("" : String))
              (c := '1') (by decide) (by decide))]
    rw [h15_empty]
    decide
  have h17 :
      (allowedWordsFinset 17).filter
          (fun w => prefixOf w 10 = ("0010010100" : String) ∧ suffixFrom w 15 = ("10" : String)) =
        ({("00100101001001010" : String), "00100101001010010"} : Finset String) := by
    rw [show
      (allowedWordsFinset 17).filter
          (fun w => prefixOf w 10 = ("0010010100" : String) ∧ suffixFrom w 15 = ("10" : String)) =
        (((allowedWordsFinset 16).filter
            (fun w => prefixOf w 10 = ("0010010100" : String) ∧ suffixFrom w 15 = ("1" : String))).biUnion
          fun w => ((K5Data.extensions w).toFinset).filter
            (fun s => suffixFrom s 15 = ("10" : String))) from by
          simpa using
            (filter_pref_suf_step (m := 10) (n := 15) (x := ("0010010100" : String)) (u := ("1" : String))
              (c := '0') (by decide) (by decide))]
    rw [h16]
    decide
  have h18 :
      (allowedWordsFinset 18).filter
          (fun w => prefixOf w 10 = ("0010010100" : String) ∧ suffixFrom w 15 = ("101" : String)) =
        ({("001001010010010101" : String), "001001010010100101"} : Finset String) := by
    rw [show
      (allowedWordsFinset 18).filter
          (fun w => prefixOf w 10 = ("0010010100" : String) ∧ suffixFrom w 15 = ("101" : String)) =
        (((allowedWordsFinset 17).filter
            (fun w => prefixOf w 10 = ("0010010100" : String) ∧ suffixFrom w 15 = ("10" : String))).biUnion
          fun w => ((K5Data.extensions w).toFinset).filter
            (fun s => suffixFrom s 15 = ("101" : String))) from by
          simpa using
            (filter_pref_suf_step (m := 10) (n := 16) (x := ("0010010100" : String)) (u := ("10" : String))
              (c := '1') (by decide) (by decide))]
    rw [h17]
    decide
  have h19 :
      (allowedWordsFinset 19).filter
          (fun w => prefixOf w 10 = ("0010010100" : String) ∧ suffixFrom w 15 = ("1010" : String)) =
        ({("0010010100100101010" : String), "0010010100101001010"} : Finset String) := by
    rw [show
      (allowedWordsFinset 19).filter
          (fun w => prefixOf w 10 = ("0010010100" : String) ∧ suffixFrom w 15 = ("1010" : String)) =
        (((allowedWordsFinset 18).filter
            (fun w => prefixOf w 10 = ("0010010100" : String) ∧ suffixFrom w 15 = ("101" : String))).biUnion
          fun w => ((K5Data.extensions w).toFinset).filter
            (fun s => suffixFrom s 15 = ("1010" : String))) from by
          simpa using
            (filter_pref_suf_step (m := 10) (n := 17) (x := ("0010010100" : String)) (u := ("101" : String))
              (c := '0') (by decide) (by decide))]
    rw [h18]
    decide
  have h20 :
      (allowedWordsFinset 20).filter
          (fun w => prefixOf w 10 = ("0010010100" : String) ∧ suffixFrom w 15 = ("10100" : String)) =
        ({("00100101001001010100" : String), "00100101001010010100"} : Finset String) := by
    rw [show
      (allowedWordsFinset 20).filter
          (fun w => prefixOf w 10 = ("0010010100" : String) ∧ suffixFrom w 15 = ("10100" : String)) =
        (((allowedWordsFinset 19).filter
            (fun w => prefixOf w 10 = ("0010010100" : String) ∧ suffixFrom w 15 = ("1010" : String))).biUnion
          fun w => ((K5Data.extensions w).toFinset).filter
            (fun s => suffixFrom s 15 = ("10100" : String))) from by
          simpa using
            (filter_pref_suf_step (m := 10) (n := 18) (x := ("0010010100" : String)) (u := ("1010" : String))
              (c := '0') (by decide) (by decide))]
    rw [h19]
    decide
  simpa [Nat.add_assoc] using h20

theorem filter_0010010100100_00_eq :
    (allowedWordsFinset (13 + 5 + 2)).filter
        (fun w => prefixOf w 13 = ("0010010100100" : String) ∧ suffixFrom w (13 + 5) = ("00" : String)) =
      ({("00100101001001010100" : String)} : Finset String) := by
  have h13_mem : ("0010010100100" : String) ∈ allowedWordsFinset 13 := by decide
  have h13 :
      (allowedWordsFinset 13).filter (fun w => prefixOf w 13 = ("0010010100100" : String)) =
        ({("0010010100100" : String)} : Finset String) :=
    filter_prefix_exact h13_mem
  have h14 :
      (allowedWordsFinset 14).filter (fun w => prefixOf w 13 = ("0010010100100" : String)) =
        ({("00100101001001" : String)} : Finset String) := by
    rw [filter_prefix_step (m := 13) (n := 12) (x := ("0010010100100" : String)) (by decide), h13]
    decide
  have h15 :
      (allowedWordsFinset 15).filter (fun w => prefixOf w 13 = ("0010010100100" : String)) =
        ({("001001010010010" : String)} : Finset String) := by
    rw [filter_prefix_step (m := 13) (n := 13) (x := ("0010010100100" : String)) (by decide), h14]
    decide
  have h16 :
      (allowedWordsFinset 16).filter (fun w => prefixOf w 13 = ("0010010100100" : String)) =
        ({("0010010100100100" : String), "0010010100100101"} : Finset String) := by
    rw [filter_prefix_step (m := 13) (n := 14) (x := ("0010010100100" : String)) (by decide), h15]
    decide
  have h17 :
      (allowedWordsFinset 17).filter (fun w => prefixOf w 13 = ("0010010100100" : String)) =
        ({("00100101001001001" : String), "00100101001001010"} : Finset String) := by
    rw [filter_prefix_step (m := 13) (n := 15) (x := ("0010010100100" : String)) (by decide), h16]
    decide
  have h18 :
      (allowedWordsFinset 18).filter (fun w => prefixOf w 13 = ("0010010100100" : String)) =
        ({("001001010010010010" : String), "001001010010010100", "001001010010010101"} :
          Finset String) := by
    rw [filter_prefix_step (m := 13) (n := 16) (x := ("0010010100100" : String)) (by decide), h17]
    decide
  have h18_empty :
      (allowedWordsFinset 18).filter
          (fun w => prefixOf w 13 = ("0010010100100" : String) ∧ suffixFrom w 18 = ("" : String)) =
        ({("001001010010010010" : String), "001001010010010100", "001001010010010101"} :
          Finset String) := by
    rw [filter_pref_suf_empty (m := 13) (L := 18) (x := ("0010010100100" : String)) (by decide), h18]
  have h19 :
      (allowedWordsFinset 19).filter
          (fun w => prefixOf w 13 = ("0010010100100" : String) ∧ suffixFrom w 18 = ("0" : String)) =
        ({("0010010100100100100" : String), "0010010100100101010"} : Finset String) := by
    rw [show
      (allowedWordsFinset 19).filter
          (fun w => prefixOf w 13 = ("0010010100100" : String) ∧ suffixFrom w 18 = ("0" : String)) =
        (((allowedWordsFinset 18).filter
            (fun w => prefixOf w 13 = ("0010010100100" : String) ∧ suffixFrom w 18 = ("" : String))).biUnion
          fun w => ((K5Data.extensions w).toFinset).filter
            (fun s => suffixFrom s 18 = ("0" : String))) from by
          simpa using
            (filter_pref_suf_step (m := 13) (n := 17) (x := ("0010010100100" : String)) (u := ("" : String))
              (c := '0') (by decide) (by decide))]
    rw [h18_empty]
    decide
  have h20 :
      (allowedWordsFinset 20).filter
          (fun w => prefixOf w 13 = ("0010010100100" : String) ∧ suffixFrom w 18 = ("00" : String)) =
        ({("00100101001001010100" : String)} : Finset String) := by
    rw [show
      (allowedWordsFinset 20).filter
          (fun w => prefixOf w 13 = ("0010010100100" : String) ∧ suffixFrom w 18 = ("00" : String)) =
        (((allowedWordsFinset 19).filter
            (fun w => prefixOf w 13 = ("0010010100100" : String) ∧ suffixFrom w 18 = ("0" : String))).biUnion
          fun w => ((K5Data.extensions w).toFinset).filter
            (fun s => suffixFrom s 18 = ("00" : String))) from by
          simpa using
            (filter_pref_suf_step (m := 13) (n := 18) (x := ("0010010100100" : String)) (u := ("0" : String))
              (c := '0') (by decide) (by decide))]
    rw [h19]
    decide
  simpa [Nat.add_assoc] using h20

end Step2Sparse

end Model

end K5Bridge

end FiniteDependence.MIS
