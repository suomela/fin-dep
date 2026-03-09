import FiniteDependence.MIS.K5Bridge.Step2SparseFiltersCore

namespace FiniteDependence.MIS

namespace K5Bridge

namespace Model

namespace Step2Sparse

theorem filter_1_0010100101_eq :
    (allowedWordsFinset (1 + 5 + 10)).filter
        (fun w => prefixOf w 1 = ("1" : String) ∧ suffixFrom w (1 + 5) = ("0010100101" : String)) =
      ({("1001010010100101" : String), "1010010010100101"} : Finset String) := by
  have h1_mem : ("1" : String) ∈ allowedWordsFinset 1 := by decide
  have h1 :
      (allowedWordsFinset 1).filter (fun w => prefixOf w 1 = ("1" : String)) =
        ({("1" : String)} : Finset String) :=
    filter_prefix_exact h1_mem
  have h2 :
      (allowedWordsFinset 2).filter (fun w => prefixOf w 1 = ("1" : String)) =
        ({("10" : String)} : Finset String) := by
    rw [filter_prefix_step (m := 1) (n := 0) (x := ("1" : String)) (by decide), h1]
    decide
  have h3 :
      (allowedWordsFinset 3).filter (fun w => prefixOf w 1 = ("1" : String)) =
        ({("100" : String), "101"} : Finset String) := by
    rw [filter_prefix_step (m := 1) (n := 1) (x := ("1" : String)) (by decide), h2]
    decide
  have h4 :
      (allowedWordsFinset 4).filter (fun w => prefixOf w 1 = ("1" : String)) =
        ({("1001" : String), "1010"} : Finset String) := by
    rw [filter_prefix_step (m := 1) (n := 2) (x := ("1" : String)) (by decide), h3]
    decide
  have h5 :
      (allowedWordsFinset 5).filter (fun w => prefixOf w 1 = ("1" : String)) =
        ({("10010" : String), "10100", "10101"} : Finset String) := by
    rw [filter_prefix_step (m := 1) (n := 3) (x := ("1" : String)) (by decide), h4]
    decide
  have h6 :
      (allowedWordsFinset 6).filter (fun w => prefixOf w 1 = ("1" : String)) =
        ({("100100" : String), "100101", "101001", "101010"} : Finset String) := by
    rw [filter_prefix_step (m := 1) (n := 4) (x := ("1" : String)) (by decide), h5]
    decide
  have h6_empty :
      (allowedWordsFinset 6).filter
          (fun w => prefixOf w 1 = ("1" : String) ∧ suffixFrom w 6 = ("" : String)) =
        ({("100100" : String), "100101", "101001", "101010"} : Finset String) := by
    rw [filter_pref_suf_empty (m := 1) (L := 6) (x := ("1" : String)) (by decide), h6]
  have h7 :
      (allowedWordsFinset 7).filter
          (fun w => prefixOf w 1 = ("1" : String) ∧ suffixFrom w 6 = ("0" : String)) =
        ({("1001010" : String), "1010010", "1010100"} : Finset String) := by
    rw [show
      (allowedWordsFinset 7).filter
          (fun w => prefixOf w 1 = ("1" : String) ∧ suffixFrom w 6 = ("0" : String)) =
        (((allowedWordsFinset 6).filter
            (fun w => prefixOf w 1 = ("1" : String) ∧ suffixFrom w 6 = ("" : String))).biUnion
          fun w => ((K5Data.extensions w).toFinset).filter
            (fun s => suffixFrom s 6 = ("0" : String))) from by
          simpa using
            (filter_pref_suf_step (m := 1) (n := 5) (x := ("1" : String)) (u := ("" : String))
              (c := '0') (by decide) (by decide))]
    rw [h6_empty]
    decide
  have h8 :
      (allowedWordsFinset 8).filter
          (fun w => prefixOf w 1 = ("1" : String) ∧ suffixFrom w 6 = ("00" : String)) =
        ({("10010100" : String), "10100100"} : Finset String) := by
    rw [show
      (allowedWordsFinset 8).filter
          (fun w => prefixOf w 1 = ("1" : String) ∧ suffixFrom w 6 = ("00" : String)) =
        (((allowedWordsFinset 7).filter
            (fun w => prefixOf w 1 = ("1" : String) ∧ suffixFrom w 6 = ("0" : String))).biUnion
          fun w => ((K5Data.extensions w).toFinset).filter
            (fun s => suffixFrom s 6 = ("00" : String))) from by
          simpa using
            (filter_pref_suf_step (m := 1) (n := 6) (x := ("1" : String)) (u := ("0" : String))
              (c := '0') (by decide) (by decide))]
    rw [h7]
    decide
  have h9 :
      (allowedWordsFinset 9).filter
          (fun w => prefixOf w 1 = ("1" : String) ∧ suffixFrom w 6 = ("001" : String)) =
        ({("100101001" : String), "101001001"} : Finset String) := by
    rw [show
      (allowedWordsFinset 9).filter
          (fun w => prefixOf w 1 = ("1" : String) ∧ suffixFrom w 6 = ("001" : String)) =
        (((allowedWordsFinset 8).filter
            (fun w => prefixOf w 1 = ("1" : String) ∧ suffixFrom w 6 = ("00" : String))).biUnion
          fun w => ((K5Data.extensions w).toFinset).filter
            (fun s => suffixFrom s 6 = ("001" : String))) from by
          simpa using
            (filter_pref_suf_step (m := 1) (n := 7) (x := ("1" : String)) (u := ("00" : String))
              (c := '1') (by decide) (by decide))]
    rw [h8]
    decide
  have h10 :
      (allowedWordsFinset 10).filter
          (fun w => prefixOf w 1 = ("1" : String) ∧ suffixFrom w 6 = ("0010" : String)) =
        ({("1001010010" : String), "1010010010"} : Finset String) := by
    rw [show
      (allowedWordsFinset 10).filter
          (fun w => prefixOf w 1 = ("1" : String) ∧ suffixFrom w 6 = ("0010" : String)) =
        (((allowedWordsFinset 9).filter
            (fun w => prefixOf w 1 = ("1" : String) ∧ suffixFrom w 6 = ("001" : String))).biUnion
          fun w => ((K5Data.extensions w).toFinset).filter
            (fun s => suffixFrom s 6 = ("0010" : String))) from by
          simpa using
            (filter_pref_suf_step (m := 1) (n := 8) (x := ("1" : String)) (u := ("001" : String))
              (c := '0') (by decide) (by decide))]
    rw [h9]
    decide
  have h11 :
      (allowedWordsFinset 11).filter
          (fun w => prefixOf w 1 = ("1" : String) ∧ suffixFrom w 6 = ("00101" : String)) =
        ({("10010100101" : String), "10100100101"} : Finset String) := by
    rw [show
      (allowedWordsFinset 11).filter
          (fun w => prefixOf w 1 = ("1" : String) ∧ suffixFrom w 6 = ("00101" : String)) =
        (((allowedWordsFinset 10).filter
            (fun w => prefixOf w 1 = ("1" : String) ∧ suffixFrom w 6 = ("0010" : String))).biUnion
          fun w => ((K5Data.extensions w).toFinset).filter
            (fun s => suffixFrom s 6 = ("00101" : String))) from by
          simpa using
            (filter_pref_suf_step (m := 1) (n := 9) (x := ("1" : String)) (u := ("0010" : String))
              (c := '1') (by decide) (by decide))]
    rw [h10]
    decide
  have h12 :
      (allowedWordsFinset 12).filter
          (fun w => prefixOf w 1 = ("1" : String) ∧ suffixFrom w 6 = ("001010" : String)) =
        ({("100101001010" : String), "101001001010"} : Finset String) := by
    rw [show
      (allowedWordsFinset 12).filter
          (fun w => prefixOf w 1 = ("1" : String) ∧ suffixFrom w 6 = ("001010" : String)) =
        (((allowedWordsFinset 11).filter
            (fun w => prefixOf w 1 = ("1" : String) ∧ suffixFrom w 6 = ("00101" : String))).biUnion
          fun w => ((K5Data.extensions w).toFinset).filter
            (fun s => suffixFrom s 6 = ("001010" : String))) from by
          simpa using
            (filter_pref_suf_step (m := 1) (n := 10) (x := ("1" : String)) (u := ("00101" : String))
              (c := '0') (by decide) (by decide))]
    rw [h11]
    decide
  have h13 :
      (allowedWordsFinset 13).filter
          (fun w => prefixOf w 1 = ("1" : String) ∧ suffixFrom w 6 = ("0010100" : String)) =
        ({("1001010010100" : String), "1010010010100"} : Finset String) := by
    rw [show
      (allowedWordsFinset 13).filter
          (fun w => prefixOf w 1 = ("1" : String) ∧ suffixFrom w 6 = ("0010100" : String)) =
        (((allowedWordsFinset 12).filter
            (fun w => prefixOf w 1 = ("1" : String) ∧ suffixFrom w 6 = ("001010" : String))).biUnion
          fun w => ((K5Data.extensions w).toFinset).filter
            (fun s => suffixFrom s 6 = ("0010100" : String))) from by
          simpa using
            (filter_pref_suf_step (m := 1) (n := 11) (x := ("1" : String)) (u := ("001010" : String))
              (c := '0') (by decide) (by decide))]
    rw [h12]
    decide
  have h14 :
      (allowedWordsFinset 14).filter
          (fun w => prefixOf w 1 = ("1" : String) ∧ suffixFrom w 6 = ("00101001" : String)) =
        ({("10010100101001" : String), "10100100101001"} : Finset String) := by
    rw [show
      (allowedWordsFinset 14).filter
          (fun w => prefixOf w 1 = ("1" : String) ∧ suffixFrom w 6 = ("00101001" : String)) =
        (((allowedWordsFinset 13).filter
            (fun w => prefixOf w 1 = ("1" : String) ∧ suffixFrom w 6 = ("0010100" : String))).biUnion
          fun w => ((K5Data.extensions w).toFinset).filter
            (fun s => suffixFrom s 6 = ("00101001" : String))) from by
          simpa using
            (filter_pref_suf_step (m := 1) (n := 12) (x := ("1" : String)) (u := ("0010100" : String))
              (c := '1') (by decide) (by decide))]
    rw [h13]
    decide
  have h15 :
      (allowedWordsFinset 15).filter
          (fun w => prefixOf w 1 = ("1" : String) ∧ suffixFrom w 6 = ("001010010" : String)) =
        ({("100101001010010" : String), "101001001010010"} : Finset String) := by
    rw [show
      (allowedWordsFinset 15).filter
          (fun w => prefixOf w 1 = ("1" : String) ∧ suffixFrom w 6 = ("001010010" : String)) =
        (((allowedWordsFinset 14).filter
            (fun w => prefixOf w 1 = ("1" : String) ∧ suffixFrom w 6 = ("00101001" : String))).biUnion
          fun w => ((K5Data.extensions w).toFinset).filter
            (fun s => suffixFrom s 6 = ("001010010" : String))) from by
          simpa using
            (filter_pref_suf_step (m := 1) (n := 13) (x := ("1" : String)) (u := ("00101001" : String))
              (c := '0') (by decide) (by decide))]
    rw [h14]
    decide
  have h16 :
      (allowedWordsFinset 16).filter
          (fun w => prefixOf w 1 = ("1" : String) ∧ suffixFrom w 6 = ("0010100101" : String)) =
        ({("1001010010100101" : String), "1010010010100101"} : Finset String) := by
    rw [show
      (allowedWordsFinset 16).filter
          (fun w => prefixOf w 1 = ("1" : String) ∧ suffixFrom w 6 = ("0010100101" : String)) =
        (((allowedWordsFinset 15).filter
            (fun w => prefixOf w 1 = ("1" : String) ∧ suffixFrom w 6 = ("001010010" : String))).biUnion
          fun w => ((K5Data.extensions w).toFinset).filter
            (fun s => suffixFrom s 6 = ("0010100101" : String))) from by
          simpa using
            (filter_pref_suf_step (m := 1) (n := 14) (x := ("1" : String)) (u := ("001010010" : String))
              (c := '1') (by decide) (by decide))]
    rw [h15]
    decide
  simpa [Nat.add_assoc] using h16

theorem filter_100_10100101_eq :
    (allowedWordsFinset (3 + 5 + 8)).filter
        (fun w => prefixOf w 3 = ("100" : String) ∧ suffixFrom w (3 + 5) = ("10100101" : String)) =
      ({("1001001010100101" : String), "1001010010100101"} : Finset String) := by
  have h3_mem : ("100" : String) ∈ allowedWordsFinset 3 := by decide
  have h3 :
      (allowedWordsFinset 3).filter (fun w => prefixOf w 3 = ("100" : String)) =
        ({("100" : String)} : Finset String) :=
    filter_prefix_exact h3_mem
  have h4 :
      (allowedWordsFinset 4).filter (fun w => prefixOf w 3 = ("100" : String)) =
        ({("1001" : String)} : Finset String) := by
    rw [filter_prefix_step (m := 3) (n := 2) (x := ("100" : String)) (by decide), h3]
    decide
  have h5 :
      (allowedWordsFinset 5).filter (fun w => prefixOf w 3 = ("100" : String)) =
        ({("10010" : String)} : Finset String) := by
    rw [filter_prefix_step (m := 3) (n := 3) (x := ("100" : String)) (by decide), h4]
    decide
  have h6 :
      (allowedWordsFinset 6).filter (fun w => prefixOf w 3 = ("100" : String)) =
        ({("100100" : String), "100101"} : Finset String) := by
    rw [filter_prefix_step (m := 3) (n := 4) (x := ("100" : String)) (by decide), h5]
    decide
  have h7 :
      (allowedWordsFinset 7).filter (fun w => prefixOf w 3 = ("100" : String)) =
        ({("1001001" : String), "1001010"} : Finset String) := by
    rw [filter_prefix_step (m := 3) (n := 5) (x := ("100" : String)) (by decide), h6]
    decide
  have h8 :
      (allowedWordsFinset 8).filter (fun w => prefixOf w 3 = ("100" : String)) =
        ({("10010010" : String), "10010100", "10010101"} : Finset String) := by
    rw [filter_prefix_step (m := 3) (n := 6) (x := ("100" : String)) (by decide), h7]
    decide
  have h8_empty :
      (allowedWordsFinset 8).filter
          (fun w => prefixOf w 3 = ("100" : String) ∧ suffixFrom w 8 = ("" : String)) =
        ({("10010010" : String), "10010100", "10010101"} : Finset String) := by
    rw [filter_pref_suf_empty (m := 3) (L := 8) (x := ("100" : String)) (by decide), h8]
  have h9 :
      (allowedWordsFinset 9).filter
          (fun w => prefixOf w 3 = ("100" : String) ∧ suffixFrom w 8 = ("1" : String)) =
        ({("100100101" : String), "100101001"} : Finset String) := by
    rw [show
      (allowedWordsFinset 9).filter
          (fun w => prefixOf w 3 = ("100" : String) ∧ suffixFrom w 8 = ("1" : String)) =
        (((allowedWordsFinset 8).filter
            (fun w => prefixOf w 3 = ("100" : String) ∧ suffixFrom w 8 = ("" : String))).biUnion
          fun w => ((K5Data.extensions w).toFinset).filter
            (fun s => suffixFrom s 8 = ("1" : String))) from by
          simpa using
            (filter_pref_suf_step (m := 3) (n := 7) (x := ("100" : String)) (u := ("" : String))
              (c := '1') (by decide) (by decide))]
    rw [h8_empty]
    decide
  have h10 :
      (allowedWordsFinset 10).filter
          (fun w => prefixOf w 3 = ("100" : String) ∧ suffixFrom w 8 = ("10" : String)) =
        ({("1001001010" : String), "1001010010"} : Finset String) := by
    rw [show
      (allowedWordsFinset 10).filter
          (fun w => prefixOf w 3 = ("100" : String) ∧ suffixFrom w 8 = ("10" : String)) =
        (((allowedWordsFinset 9).filter
            (fun w => prefixOf w 3 = ("100" : String) ∧ suffixFrom w 8 = ("1" : String))).biUnion
          fun w => ((K5Data.extensions w).toFinset).filter
            (fun s => suffixFrom s 8 = ("10" : String))) from by
          simpa using
            (filter_pref_suf_step (m := 3) (n := 8) (x := ("100" : String)) (u := ("1" : String))
              (c := '0') (by decide) (by decide))]
    rw [h9]
    decide
  have h11 :
      (allowedWordsFinset 11).filter
          (fun w => prefixOf w 3 = ("100" : String) ∧ suffixFrom w 8 = ("101" : String)) =
        ({("10010010101" : String), "10010100101"} : Finset String) := by
    rw [show
      (allowedWordsFinset 11).filter
          (fun w => prefixOf w 3 = ("100" : String) ∧ suffixFrom w 8 = ("101" : String)) =
        (((allowedWordsFinset 10).filter
            (fun w => prefixOf w 3 = ("100" : String) ∧ suffixFrom w 8 = ("10" : String))).biUnion
          fun w => ((K5Data.extensions w).toFinset).filter
            (fun s => suffixFrom s 8 = ("101" : String))) from by
          simpa using
            (filter_pref_suf_step (m := 3) (n := 9) (x := ("100" : String)) (u := ("10" : String))
              (c := '1') (by decide) (by decide))]
    rw [h10]
    decide
  have h12 :
      (allowedWordsFinset 12).filter
          (fun w => prefixOf w 3 = ("100" : String) ∧ suffixFrom w 8 = ("1010" : String)) =
        ({("100100101010" : String), "100101001010"} : Finset String) := by
    rw [show
      (allowedWordsFinset 12).filter
          (fun w => prefixOf w 3 = ("100" : String) ∧ suffixFrom w 8 = ("1010" : String)) =
        (((allowedWordsFinset 11).filter
            (fun w => prefixOf w 3 = ("100" : String) ∧ suffixFrom w 8 = ("101" : String))).biUnion
          fun w => ((K5Data.extensions w).toFinset).filter
            (fun s => suffixFrom s 8 = ("1010" : String))) from by
          simpa using
            (filter_pref_suf_step (m := 3) (n := 10) (x := ("100" : String)) (u := ("101" : String))
              (c := '0') (by decide) (by decide))]
    rw [h11]
    decide
  have h13 :
      (allowedWordsFinset 13).filter
          (fun w => prefixOf w 3 = ("100" : String) ∧ suffixFrom w 8 = ("10100" : String)) =
        ({("1001001010100" : String), "1001010010100"} : Finset String) := by
    rw [show
      (allowedWordsFinset 13).filter
          (fun w => prefixOf w 3 = ("100" : String) ∧ suffixFrom w 8 = ("10100" : String)) =
        (((allowedWordsFinset 12).filter
            (fun w => prefixOf w 3 = ("100" : String) ∧ suffixFrom w 8 = ("1010" : String))).biUnion
          fun w => ((K5Data.extensions w).toFinset).filter
            (fun s => suffixFrom s 8 = ("10100" : String))) from by
          simpa using
            (filter_pref_suf_step (m := 3) (n := 11) (x := ("100" : String)) (u := ("1010" : String))
              (c := '0') (by decide) (by decide))]
    rw [h12]
    decide
  have h14 :
      (allowedWordsFinset 14).filter
          (fun w => prefixOf w 3 = ("100" : String) ∧ suffixFrom w 8 = ("101001" : String)) =
        ({("10010010101001" : String), "10010100101001"} : Finset String) := by
    rw [show
      (allowedWordsFinset 14).filter
          (fun w => prefixOf w 3 = ("100" : String) ∧ suffixFrom w 8 = ("101001" : String)) =
        (((allowedWordsFinset 13).filter
            (fun w => prefixOf w 3 = ("100" : String) ∧ suffixFrom w 8 = ("10100" : String))).biUnion
          fun w => ((K5Data.extensions w).toFinset).filter
            (fun s => suffixFrom s 8 = ("101001" : String))) from by
          simpa using
            (filter_pref_suf_step (m := 3) (n := 12) (x := ("100" : String)) (u := ("10100" : String))
              (c := '1') (by decide) (by decide))]
    rw [h13]
    decide
  have h15 :
      (allowedWordsFinset 15).filter
          (fun w => prefixOf w 3 = ("100" : String) ∧ suffixFrom w 8 = ("1010010" : String)) =
        ({("100100101010010" : String), "100101001010010"} : Finset String) := by
    rw [show
      (allowedWordsFinset 15).filter
          (fun w => prefixOf w 3 = ("100" : String) ∧ suffixFrom w 8 = ("1010010" : String)) =
        (((allowedWordsFinset 14).filter
            (fun w => prefixOf w 3 = ("100" : String) ∧ suffixFrom w 8 = ("101001" : String))).biUnion
          fun w => ((K5Data.extensions w).toFinset).filter
            (fun s => suffixFrom s 8 = ("1010010" : String))) from by
          simpa using
            (filter_pref_suf_step (m := 3) (n := 13) (x := ("100" : String)) (u := ("101001" : String))
              (c := '0') (by decide) (by decide))]
    rw [h14]
    decide
  have h16 :
      (allowedWordsFinset 16).filter
          (fun w => prefixOf w 3 = ("100" : String) ∧ suffixFrom w 8 = ("10100101" : String)) =
        ({("1001001010100101" : String), "1001010010100101"} : Finset String) := by
    rw [show
      (allowedWordsFinset 16).filter
          (fun w => prefixOf w 3 = ("100" : String) ∧ suffixFrom w 8 = ("10100101" : String)) =
        (((allowedWordsFinset 15).filter
            (fun w => prefixOf w 3 = ("100" : String) ∧ suffixFrom w 8 = ("1010010" : String))).biUnion
          fun w => ((K5Data.extensions w).toFinset).filter
            (fun s => suffixFrom s 8 = ("10100101" : String))) from by
          simpa using
            (filter_pref_suf_step (m := 3) (n := 14) (x := ("100" : String)) (u := ("1010010" : String))
              (c := '1') (by decide) (by decide))]
    rw [h15]
    decide
  simpa [Nat.add_assoc] using h16

theorem filter_10100_001001_eq :
    (allowedWordsFinset (5 + 5 + 6)).filter
        (fun w => prefixOf w 5 = ("10100" : String) ∧ suffixFrom w (5 + 5) = ("001001" : String)) =
      ({("1010010101001001" : String)} : Finset String) := by
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
          (fun w => prefixOf w 5 = ("10100" : String) ∧ suffixFrom w 10 = ("0" : String)) =
        ({("10100100100" : String), "10100101010"} : Finset String) := by
    have hstep :
        (allowedWordsFinset 11).filter
            (fun w => prefixOf w 5 = ("10100" : String) ∧ suffixFrom w 10 = ("0" : String)) =
          (((allowedWordsFinset 10).filter
              (fun w => prefixOf w 5 = ("10100" : String) ∧ suffixFrom w 10 = ("" : String))).biUnion
            fun w => ((K5Data.extensions w).toFinset).filter
              (fun s => suffixFrom s 10 = ("0" : String))) := by
      change (allowedWordsFinset 11).filter
          (fun w => prefixOf w 5 = ("10100" : String) ∧ suffixFrom w 10 = (("" : String).push '0')) =
        (((allowedWordsFinset 10).filter
            (fun w => prefixOf w 5 = ("10100" : String) ∧ suffixFrom w 10 = ("" : String))).biUnion
          fun w => ((K5Data.extensions w).toFinset).filter
            (fun s => suffixFrom s 10 = (("" : String).push '0')))
      exact filter_pref_suf_step (m := 5) (n := 9) (x := ("10100" : String)) (u := ("" : String))
        (c := '0') (by decide) (by decide)
    rw [hstep]
    rw [h10_empty]
    decide
  have h12 :
      (allowedWordsFinset 12).filter
          (fun w => prefixOf w 5 = ("10100" : String) ∧ suffixFrom w 10 = ("00" : String)) =
        ({("101001010100" : String)} : Finset String) := by
    have hstep :
        (allowedWordsFinset 12).filter
            (fun w => prefixOf w 5 = ("10100" : String) ∧ suffixFrom w 10 = ("00" : String)) =
          (((allowedWordsFinset 11).filter
              (fun w => prefixOf w 5 = ("10100" : String) ∧ suffixFrom w 10 = ("0" : String))).biUnion
            fun w => ((K5Data.extensions w).toFinset).filter
              (fun s => suffixFrom s 10 = ("00" : String))) := by
      change (allowedWordsFinset 12).filter
          (fun w => prefixOf w 5 = ("10100" : String) ∧ suffixFrom w 10 = (("0" : String).push '0')) =
        (((allowedWordsFinset 11).filter
            (fun w => prefixOf w 5 = ("10100" : String) ∧ suffixFrom w 10 = ("0" : String))).biUnion
          fun w => ((K5Data.extensions w).toFinset).filter
            (fun s => suffixFrom s 10 = (("0" : String).push '0')))
      exact filter_pref_suf_step (m := 5) (n := 10) (x := ("10100" : String)) (u := ("0" : String))
        (c := '0') (by decide) (by decide)
    rw [hstep]
    rw [h11]
    decide
  have h13 :
      (allowedWordsFinset 13).filter
          (fun w => prefixOf w 5 = ("10100" : String) ∧ suffixFrom w 10 = ("001" : String)) =
        ({("1010010101001" : String)} : Finset String) := by
    have hstep :
        (allowedWordsFinset 13).filter
            (fun w => prefixOf w 5 = ("10100" : String) ∧ suffixFrom w 10 = ("001" : String)) =
          (((allowedWordsFinset 12).filter
              (fun w => prefixOf w 5 = ("10100" : String) ∧ suffixFrom w 10 = ("00" : String))).biUnion
            fun w => ((K5Data.extensions w).toFinset).filter
              (fun s => suffixFrom s 10 = ("001" : String))) := by
      change (allowedWordsFinset 13).filter
          (fun w => prefixOf w 5 = ("10100" : String) ∧ suffixFrom w 10 = (("00" : String).push '1')) =
        (((allowedWordsFinset 12).filter
            (fun w => prefixOf w 5 = ("10100" : String) ∧ suffixFrom w 10 = ("00" : String))).biUnion
          fun w => ((K5Data.extensions w).toFinset).filter
            (fun s => suffixFrom s 10 = (("00" : String).push '1')))
      exact filter_pref_suf_step (m := 5) (n := 11) (x := ("10100" : String)) (u := ("00" : String))
        (c := '1') (by decide) (by decide)
    rw [hstep]
    rw [h12]
    decide
  have h14 :
      (allowedWordsFinset 14).filter
          (fun w => prefixOf w 5 = ("10100" : String) ∧ suffixFrom w 10 = ("0010" : String)) =
        ({("10100101010010" : String)} : Finset String) := by
    have hstep :
        (allowedWordsFinset 14).filter
            (fun w => prefixOf w 5 = ("10100" : String) ∧ suffixFrom w 10 = ("0010" : String)) =
          (((allowedWordsFinset 13).filter
              (fun w => prefixOf w 5 = ("10100" : String) ∧ suffixFrom w 10 = ("001" : String))).biUnion
            fun w => ((K5Data.extensions w).toFinset).filter
              (fun s => suffixFrom s 10 = ("0010" : String))) := by
      change (allowedWordsFinset 14).filter
          (fun w => prefixOf w 5 = ("10100" : String) ∧ suffixFrom w 10 = (("001" : String).push '0')) =
        (((allowedWordsFinset 13).filter
            (fun w => prefixOf w 5 = ("10100" : String) ∧ suffixFrom w 10 = ("001" : String))).biUnion
          fun w => ((K5Data.extensions w).toFinset).filter
            (fun s => suffixFrom s 10 = (("001" : String).push '0')))
      exact filter_pref_suf_step (m := 5) (n := 12) (x := ("10100" : String)) (u := ("001" : String))
        (c := '0') (by decide) (by decide)
    rw [hstep]
    rw [h13]
    decide
  have h15 :
      (allowedWordsFinset 15).filter
          (fun w => prefixOf w 5 = ("10100" : String) ∧ suffixFrom w 10 = ("00100" : String)) =
        ({("101001010100100" : String)} : Finset String) := by
    have hstep :
        (allowedWordsFinset 15).filter
            (fun w => prefixOf w 5 = ("10100" : String) ∧ suffixFrom w 10 = ("00100" : String)) =
          (((allowedWordsFinset 14).filter
              (fun w => prefixOf w 5 = ("10100" : String) ∧ suffixFrom w 10 = ("0010" : String))).biUnion
            fun w => ((K5Data.extensions w).toFinset).filter
              (fun s => suffixFrom s 10 = ("00100" : String))) := by
      change (allowedWordsFinset 15).filter
          (fun w => prefixOf w 5 = ("10100" : String) ∧ suffixFrom w 10 = (("0010" : String).push '0')) =
        (((allowedWordsFinset 14).filter
            (fun w => prefixOf w 5 = ("10100" : String) ∧ suffixFrom w 10 = ("0010" : String))).biUnion
          fun w => ((K5Data.extensions w).toFinset).filter
            (fun s => suffixFrom s 10 = (("0010" : String).push '0')))
      exact filter_pref_suf_step (m := 5) (n := 13) (x := ("10100" : String)) (u := ("0010" : String))
        (c := '0') (by decide) (by decide)
    rw [hstep]
    rw [h14]
    decide
  have h16 :
      (allowedWordsFinset 16).filter
          (fun w => prefixOf w 5 = ("10100" : String) ∧ suffixFrom w 10 = ("001001" : String)) =
        ({("1010010101001001" : String)} : Finset String) := by
    have hstep :
        (allowedWordsFinset 16).filter
            (fun w => prefixOf w 5 = ("10100" : String) ∧ suffixFrom w 10 = ("001001" : String)) =
          (((allowedWordsFinset 15).filter
              (fun w => prefixOf w 5 = ("10100" : String) ∧ suffixFrom w 10 = ("00100" : String))).biUnion
            fun w => ((K5Data.extensions w).toFinset).filter
              (fun s => suffixFrom s 10 = ("001001" : String))) := by
      change (allowedWordsFinset 16).filter
          (fun w => prefixOf w 5 = ("10100" : String) ∧ suffixFrom w 10 = (("00100" : String).push '1')) =
        (((allowedWordsFinset 15).filter
            (fun w => prefixOf w 5 = ("10100" : String) ∧ suffixFrom w 10 = ("00100" : String))).biUnion
          fun w => ((K5Data.extensions w).toFinset).filter
            (fun s => suffixFrom s 10 = (("00100" : String).push '1')))
      exact filter_pref_suf_step (m := 5) (n := 14) (x := ("10100" : String)) (u := ("00100" : String))
        (c := '1') (by decide) (by decide)
    rw [hstep]
    rw [h15]
    decide
  simpa [Nat.add_assoc] using h16

end Step2Sparse

end Model

end K5Bridge

end FiniteDependence.MIS
