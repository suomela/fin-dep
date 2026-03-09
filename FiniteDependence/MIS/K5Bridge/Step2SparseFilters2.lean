import FiniteDependence.MIS.K5Bridge.Step2SparseFiltersCore

namespace FiniteDependence.MIS

namespace K5Bridge

namespace Model

namespace Step2Sparse

theorem filter_10100_100101_eq :
    (allowedWordsFinset (5 + 5 + 6)).filter
        (fun w => prefixOf w 5 = ("10100" : String) ∧ suffixFrom w (5 + 5) = ("100101" : String)) =
      ({("1010010010100101" : String), "1010010100100101"} : Finset String) := by
  have h5_mem : ("10100" : String) ∈ allowedWordsFinset 5 := by decide
  have h5 :
      (allowedWordsFinset 5).filter (fun w => prefixOf w 5 = ("10100" : String)) =
        ({("10100" : String)} : Finset String) :=
    filter_prefix_exact h5_mem
  have h6 :
      (allowedWordsFinset 6).filter (fun w => prefixOf w 5 = ("10100" : String)) =
        ({("101001" : String)} : Finset String) := by
    rw [filter_prefix_step (m := 5) (n := 4) (x := ("10100" : String)) (by decide), h5]
    decide
  have h7 :
      (allowedWordsFinset 7).filter (fun w => prefixOf w 5 = ("10100" : String)) =
        ({("1010010" : String)} : Finset String) := by
    rw [filter_prefix_step (m := 5) (n := 5) (x := ("10100" : String)) (by decide), h6]
    decide
  have h8 :
      (allowedWordsFinset 8).filter (fun w => prefixOf w 5 = ("10100" : String)) =
        ({("10100100" : String), "10100101"} : Finset String) := by
    rw [filter_prefix_step (m := 5) (n := 6) (x := ("10100" : String)) (by decide), h7]
    decide
  have h9 :
      (allowedWordsFinset 9).filter (fun w => prefixOf w 5 = ("10100" : String)) =
        ({("101001001" : String), "101001010"} : Finset String) := by
    rw [filter_prefix_step (m := 5) (n := 7) (x := ("10100" : String)) (by decide), h8]
    decide
  have h10 :
      (allowedWordsFinset 10).filter (fun w => prefixOf w 5 = ("10100" : String)) =
        ({("1010010010" : String), "1010010100", "1010010101"} : Finset String) := by
    rw [filter_prefix_step (m := 5) (n := 8) (x := ("10100" : String)) (by decide), h9]
    decide
  have h10_empty :
      (allowedWordsFinset 10).filter
          (fun w => prefixOf w 5 = ("10100" : String) ∧ suffixFrom w 10 = ("" : String)) =
        ({("1010010010" : String), "1010010100", "1010010101"} : Finset String) := by
    rw [filter_pref_suf_empty (m := 5) (L := 10) (x := ("10100" : String)) (by decide), h10]
  have h11 :
      (allowedWordsFinset 11).filter
          (fun w => prefixOf w 5 = ("10100" : String) ∧ suffixFrom w 10 = ("1" : String)) =
        ({("10100100101" : String), "10100101001"} : Finset String) := by
    rw [show
      (allowedWordsFinset 11).filter
          (fun w => prefixOf w 5 = ("10100" : String) ∧ suffixFrom w 10 = ("1" : String)) =
        (((allowedWordsFinset 10).filter
            (fun w => prefixOf w 5 = ("10100" : String) ∧ suffixFrom w 10 = ("" : String))).biUnion
          fun w => ((K5Data.extensions w).toFinset).filter
            (fun s => suffixFrom s 10 = ("1" : String))) from by
          simpa using
            (filter_pref_suf_step (m := 5) (n := 9) (x := ("10100" : String)) (u := ("" : String))
              (c := '1') (by decide) (by decide))]
    rw [h10_empty]
    decide
  have h12 :
      (allowedWordsFinset 12).filter
          (fun w => prefixOf w 5 = ("10100" : String) ∧ suffixFrom w 10 = ("10" : String)) =
        ({("101001001010" : String), "101001010010"} : Finset String) := by
    rw [show
      (allowedWordsFinset 12).filter
          (fun w => prefixOf w 5 = ("10100" : String) ∧ suffixFrom w 10 = ("10" : String)) =
        (((allowedWordsFinset 11).filter
            (fun w => prefixOf w 5 = ("10100" : String) ∧ suffixFrom w 10 = ("1" : String))).biUnion
          fun w => ((K5Data.extensions w).toFinset).filter
            (fun s => suffixFrom s 10 = ("10" : String))) from by
          simpa using
            (filter_pref_suf_step (m := 5) (n := 10) (x := ("10100" : String)) (u := ("1" : String))
              (c := '0') (by decide) (by decide))]
    rw [h11]
    decide
  have h13 :
      (allowedWordsFinset 13).filter
          (fun w => prefixOf w 5 = ("10100" : String) ∧ suffixFrom w 10 = ("100" : String)) =
        ({("1010010010100" : String), "1010010100100"} : Finset String) := by
    rw [show
      (allowedWordsFinset 13).filter
          (fun w => prefixOf w 5 = ("10100" : String) ∧ suffixFrom w 10 = ("100" : String)) =
        (((allowedWordsFinset 12).filter
            (fun w => prefixOf w 5 = ("10100" : String) ∧ suffixFrom w 10 = ("10" : String))).biUnion
          fun w => ((K5Data.extensions w).toFinset).filter
            (fun s => suffixFrom s 10 = ("100" : String))) from by
          simpa using
            (filter_pref_suf_step (m := 5) (n := 11) (x := ("10100" : String)) (u := ("10" : String))
              (c := '0') (by decide) (by decide))]
    rw [h12]
    decide
  have h14 :
      (allowedWordsFinset 14).filter
          (fun w => prefixOf w 5 = ("10100" : String) ∧ suffixFrom w 10 = ("1001" : String)) =
        ({("10100100101001" : String), "10100101001001"} : Finset String) := by
    rw [show
      (allowedWordsFinset 14).filter
          (fun w => prefixOf w 5 = ("10100" : String) ∧ suffixFrom w 10 = ("1001" : String)) =
        (((allowedWordsFinset 13).filter
            (fun w => prefixOf w 5 = ("10100" : String) ∧ suffixFrom w 10 = ("100" : String))).biUnion
          fun w => ((K5Data.extensions w).toFinset).filter
            (fun s => suffixFrom s 10 = ("1001" : String))) from by
          simpa using
            (filter_pref_suf_step (m := 5) (n := 12) (x := ("10100" : String)) (u := ("100" : String))
              (c := '1') (by decide) (by decide))]
    rw [h13]
    decide
  have h15 :
      (allowedWordsFinset 15).filter
          (fun w => prefixOf w 5 = ("10100" : String) ∧ suffixFrom w 10 = ("10010" : String)) =
        ({("101001001010010" : String), "101001010010010"} : Finset String) := by
    rw [show
      (allowedWordsFinset 15).filter
          (fun w => prefixOf w 5 = ("10100" : String) ∧ suffixFrom w 10 = ("10010" : String)) =
        (((allowedWordsFinset 14).filter
            (fun w => prefixOf w 5 = ("10100" : String) ∧ suffixFrom w 10 = ("1001" : String))).biUnion
          fun w => ((K5Data.extensions w).toFinset).filter
            (fun s => suffixFrom s 10 = ("10010" : String))) from by
          simpa using
            (filter_pref_suf_step (m := 5) (n := 13) (x := ("10100" : String)) (u := ("1001" : String))
              (c := '0') (by decide) (by decide))]
    rw [h14]
    decide
  have h16 :
      (allowedWordsFinset 16).filter
          (fun w => prefixOf w 5 = ("10100" : String) ∧ suffixFrom w 10 = ("100101" : String)) =
        ({("1010010010100101" : String), "1010010100100101"} : Finset String) := by
    rw [show
      (allowedWordsFinset 16).filter
          (fun w => prefixOf w 5 = ("10100" : String) ∧ suffixFrom w 10 = ("100101" : String)) =
        (((allowedWordsFinset 15).filter
            (fun w => prefixOf w 5 = ("10100" : String) ∧ suffixFrom w 10 = ("10010" : String))).biUnion
          fun w => ((K5Data.extensions w).toFinset).filter
            (fun s => suffixFrom s 10 = ("100101" : String))) from by
          simpa using
            (filter_pref_suf_step (m := 5) (n := 14) (x := ("10100" : String)) (u := ("10010" : String))
              (c := '1') (by decide) (by decide))]
    rw [h15]
    decide
  simpa [Nat.add_assoc] using h16

theorem filter_100100_00101_eq :
    (allowedWordsFinset (6 + 5 + 5)).filter
        (fun w => prefixOf w 6 = ("100100" : String) ∧ suffixFrom w (6 + 5) = ("00101" : String)) =
      ({("1001001010100101" : String)} : Finset String) := by
  have h6_mem : ("100100" : String) ∈ allowedWordsFinset 6 := by decide
  have h6 :
      (allowedWordsFinset 6).filter (fun w => prefixOf w 6 = ("100100" : String)) =
        ({("100100" : String)} : Finset String) :=
    filter_prefix_exact h6_mem
  have h7 :
      (allowedWordsFinset 7).filter (fun w => prefixOf w 6 = ("100100" : String)) =
        ({("1001001" : String)} : Finset String) := by
    rw [filter_prefix_step (m := 6) (n := 5) (x := ("100100" : String)) (by decide), h6]
    decide
  have h8 :
      (allowedWordsFinset 8).filter (fun w => prefixOf w 6 = ("100100" : String)) =
        ({("10010010" : String)} : Finset String) := by
    rw [filter_prefix_step (m := 6) (n := 6) (x := ("100100" : String)) (by decide), h7]
    decide
  have h9 :
      (allowedWordsFinset 9).filter (fun w => prefixOf w 6 = ("100100" : String)) =
        ({("100100100" : String), "100100101"} : Finset String) := by
    rw [filter_prefix_step (m := 6) (n := 7) (x := ("100100" : String)) (by decide), h8]
    decide
  have h10 :
      (allowedWordsFinset 10).filter (fun w => prefixOf w 6 = ("100100" : String)) =
        ({("1001001001" : String), "1001001010"} : Finset String) := by
    rw [filter_prefix_step (m := 6) (n := 8) (x := ("100100" : String)) (by decide), h9]
    decide
  have h11 :
      (allowedWordsFinset 11).filter (fun w => prefixOf w 6 = ("100100" : String)) =
        ({("10010010010" : String), "10010010100", "10010010101"} : Finset String) := by
    rw [filter_prefix_step (m := 6) (n := 9) (x := ("100100" : String)) (by decide), h10]
    decide
  have h11_empty :
      (allowedWordsFinset 11).filter
          (fun w => prefixOf w 6 = ("100100" : String) ∧ suffixFrom w 11 = ("" : String)) =
        ({("10010010010" : String), "10010010100", "10010010101"} : Finset String) := by
    rw [filter_pref_suf_empty (m := 6) (L := 11) (x := ("100100" : String)) (by decide), h11]
  have h12 :
      (allowedWordsFinset 12).filter
          (fun w => prefixOf w 6 = ("100100" : String) ∧ suffixFrom w 11 = ("0" : String)) =
        ({("100100100100" : String), "100100101010"} : Finset String) := by
    rw [show
      (allowedWordsFinset 12).filter
          (fun w => prefixOf w 6 = ("100100" : String) ∧ suffixFrom w 11 = ("0" : String)) =
        (((allowedWordsFinset 11).filter
            (fun w => prefixOf w 6 = ("100100" : String) ∧ suffixFrom w 11 = ("" : String))).biUnion
          fun w => ((K5Data.extensions w).toFinset).filter
            (fun s => suffixFrom s 11 = ("0" : String))) from by
          simpa using
            (filter_pref_suf_step (m := 6) (n := 10) (x := ("100100" : String)) (u := ("" : String))
              (c := '0') (by decide) (by decide))]
    rw [h11_empty]
    decide
  have h13 :
      (allowedWordsFinset 13).filter
          (fun w => prefixOf w 6 = ("100100" : String) ∧ suffixFrom w 11 = ("00" : String)) =
        ({("1001001010100" : String)} : Finset String) := by
    rw [show
      (allowedWordsFinset 13).filter
          (fun w => prefixOf w 6 = ("100100" : String) ∧ suffixFrom w 11 = ("00" : String)) =
        (((allowedWordsFinset 12).filter
            (fun w => prefixOf w 6 = ("100100" : String) ∧ suffixFrom w 11 = ("0" : String))).biUnion
          fun w => ((K5Data.extensions w).toFinset).filter
            (fun s => suffixFrom s 11 = ("00" : String))) from by
          simpa using
            (filter_pref_suf_step (m := 6) (n := 11) (x := ("100100" : String)) (u := ("0" : String))
              (c := '0') (by decide) (by decide))]
    rw [h12]
    decide
  have h14 :
      (allowedWordsFinset 14).filter
          (fun w => prefixOf w 6 = ("100100" : String) ∧ suffixFrom w 11 = ("001" : String)) =
        ({("10010010101001" : String)} : Finset String) := by
    rw [show
      (allowedWordsFinset 14).filter
          (fun w => prefixOf w 6 = ("100100" : String) ∧ suffixFrom w 11 = ("001" : String)) =
        (((allowedWordsFinset 13).filter
            (fun w => prefixOf w 6 = ("100100" : String) ∧ suffixFrom w 11 = ("00" : String))).biUnion
          fun w => ((K5Data.extensions w).toFinset).filter
            (fun s => suffixFrom s 11 = ("001" : String))) from by
          simpa using
            (filter_pref_suf_step (m := 6) (n := 12) (x := ("100100" : String)) (u := ("00" : String))
              (c := '1') (by decide) (by decide))]
    rw [h13]
    decide
  have h15 :
      (allowedWordsFinset 15).filter
          (fun w => prefixOf w 6 = ("100100" : String) ∧ suffixFrom w 11 = ("0010" : String)) =
        ({("100100101010010" : String)} : Finset String) := by
    rw [show
      (allowedWordsFinset 15).filter
          (fun w => prefixOf w 6 = ("100100" : String) ∧ suffixFrom w 11 = ("0010" : String)) =
        (((allowedWordsFinset 14).filter
            (fun w => prefixOf w 6 = ("100100" : String) ∧ suffixFrom w 11 = ("001" : String))).biUnion
          fun w => ((K5Data.extensions w).toFinset).filter
            (fun s => suffixFrom s 11 = ("0010" : String))) from by
          simpa using
            (filter_pref_suf_step (m := 6) (n := 13) (x := ("100100" : String)) (u := ("001" : String))
              (c := '0') (by decide) (by decide))]
    rw [h14]
    decide
  have h16 :
      (allowedWordsFinset 16).filter
          (fun w => prefixOf w 6 = ("100100" : String) ∧ suffixFrom w 11 = ("00101" : String)) =
        ({("1001001010100101" : String)} : Finset String) := by
    rw [show
      (allowedWordsFinset 16).filter
          (fun w => prefixOf w 6 = ("100100" : String) ∧ suffixFrom w 11 = ("00101" : String)) =
        (((allowedWordsFinset 15).filter
            (fun w => prefixOf w 6 = ("100100" : String) ∧ suffixFrom w 11 = ("0010" : String))).biUnion
          fun w => ((K5Data.extensions w).toFinset).filter
            (fun s => suffixFrom s 11 = ("00101" : String))) from by
          simpa using
            (filter_pref_suf_step (m := 6) (n := 14) (x := ("100100" : String)) (u := ("0010" : String))
              (c := '1') (by decide) (by decide))]
    rw [h15]
    decide
  simpa [Nat.add_assoc] using h16

theorem filter_10100101_101_eq :
    (allowedWordsFinset (8 + 5 + 3)).filter
        (fun w => prefixOf w 8 = ("10100101" : String) ∧ suffixFrom w (8 + 5) = ("101" : String)) =
      ({("1010010100100101" : String), "1010010101010101"} : Finset String) := by
  have h8_mem : ("10100101" : String) ∈ allowedWordsFinset 8 := by decide
  have h8 :
      (allowedWordsFinset 8).filter (fun w => prefixOf w 8 = ("10100101" : String)) =
        ({("10100101" : String)} : Finset String) :=
    filter_prefix_exact h8_mem
  have h9 :
      (allowedWordsFinset 9).filter (fun w => prefixOf w 8 = ("10100101" : String)) =
        ({("101001010" : String)} : Finset String) := by
    rw [filter_prefix_step (m := 8) (n := 7) (x := ("10100101" : String)) (by decide), h8]
    decide
  have h10 :
      (allowedWordsFinset 10).filter (fun w => prefixOf w 8 = ("10100101" : String)) =
        ({("1010010100" : String), "1010010101"} : Finset String) := by
    rw [filter_prefix_step (m := 8) (n := 8) (x := ("10100101" : String)) (by decide), h9]
    decide
  have h11 :
      (allowedWordsFinset 11).filter (fun w => prefixOf w 8 = ("10100101" : String)) =
        ({("10100101001" : String), "10100101010"} : Finset String) := by
    rw [filter_prefix_step (m := 8) (n := 9) (x := ("10100101" : String)) (by decide), h10]
    decide
  have h12 :
      (allowedWordsFinset 12).filter (fun w => prefixOf w 8 = ("10100101" : String)) =
        ({("101001010010" : String), "101001010100", "101001010101"} : Finset String) := by
    rw [filter_prefix_step (m := 8) (n := 10) (x := ("10100101" : String)) (by decide), h11]
    decide
  have h13 :
      (allowedWordsFinset 13).filter (fun w => prefixOf w 8 = ("10100101" : String)) =
        ({("1010010100100" : String), "1010010100101", "1010010101001", "1010010101010"} :
          Finset String) := by
    rw [filter_prefix_step (m := 8) (n := 11) (x := ("10100101" : String)) (by decide), h12]
    decide
  have h13_empty :
      (allowedWordsFinset 13).filter
          (fun w => prefixOf w 8 = ("10100101" : String) ∧ suffixFrom w 13 = ("" : String)) =
        ({("1010010100100" : String), "1010010100101", "1010010101001", "1010010101010"} :
          Finset String) := by
    rw [filter_pref_suf_empty (m := 8) (L := 13) (x := ("10100101" : String)) (by decide), h13]
  have h14 :
      (allowedWordsFinset 14).filter
          (fun w => prefixOf w 8 = ("10100101" : String) ∧ suffixFrom w 13 = ("1" : String)) =
        ({("10100101001001" : String), "10100101010101"} : Finset String) := by
    rw [show
      (allowedWordsFinset 14).filter
          (fun w => prefixOf w 8 = ("10100101" : String) ∧ suffixFrom w 13 = ("1" : String)) =
        (((allowedWordsFinset 13).filter
            (fun w => prefixOf w 8 = ("10100101" : String) ∧ suffixFrom w 13 = ("" : String))).biUnion
          fun w => ((K5Data.extensions w).toFinset).filter
            (fun s => suffixFrom s 13 = ("1" : String))) from by
          simpa using
            (filter_pref_suf_step (m := 8) (n := 12) (x := ("10100101" : String)) (u := ("" : String))
              (c := '1') (by decide) (by decide))]
    rw [h13_empty]
    decide
  have h15 :
      (allowedWordsFinset 15).filter
          (fun w => prefixOf w 8 = ("10100101" : String) ∧ suffixFrom w 13 = ("10" : String)) =
        ({("101001010010010" : String), "101001010101010"} : Finset String) := by
    rw [show
      (allowedWordsFinset 15).filter
          (fun w => prefixOf w 8 = ("10100101" : String) ∧ suffixFrom w 13 = ("10" : String)) =
        (((allowedWordsFinset 14).filter
            (fun w => prefixOf w 8 = ("10100101" : String) ∧ suffixFrom w 13 = ("1" : String))).biUnion
          fun w => ((K5Data.extensions w).toFinset).filter
            (fun s => suffixFrom s 13 = ("10" : String))) from by
          simpa using
            (filter_pref_suf_step (m := 8) (n := 13) (x := ("10100101" : String)) (u := ("1" : String))
              (c := '0') (by decide) (by decide))]
    rw [h14]
    decide
  have h16 :
      (allowedWordsFinset 16).filter
          (fun w => prefixOf w 8 = ("10100101" : String) ∧ suffixFrom w 13 = ("101" : String)) =
        ({("1010010100100101" : String), "1010010101010101"} : Finset String) := by
    rw [show
      (allowedWordsFinset 16).filter
          (fun w => prefixOf w 8 = ("10100101" : String) ∧ suffixFrom w 13 = ("101" : String)) =
        (((allowedWordsFinset 15).filter
            (fun w => prefixOf w 8 = ("10100101" : String) ∧ suffixFrom w 13 = ("10" : String))).biUnion
          fun w => ((K5Data.extensions w).toFinset).filter
            (fun s => suffixFrom s 13 = ("101" : String))) from by
          simpa using
            (filter_pref_suf_step (m := 8) (n := 14) (x := ("10100101" : String)) (u := ("10" : String))
              (c := '1') (by decide) (by decide))]
    rw [h15]
    decide
  simpa [Nat.add_assoc] using h16

end Step2Sparse

end Model

end K5Bridge

end FiniteDependence.MIS
