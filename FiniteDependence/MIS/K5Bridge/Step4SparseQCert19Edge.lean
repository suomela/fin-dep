import FiniteDependence.MIS.K5Bridge.Step2SparseFiltersCore

namespace FiniteDependence.MIS

namespace K5Bridge

namespace Model

noncomputable section

set_option maxRecDepth 1000000
set_option maxHeartbeats 20000000

namespace Step4Sparse

open Step2Sparse

theorem filter19_edge_eq :
    (allowedWordsFinset (7 + 5 + 7)).filter
        (fun w => prefixOf w 7 = ("0010101" : String) ∧ suffixFrom w (7 + 5) = ("0010100" : String)) =
      ({("0010101001010010100" : String), "0010101010010010100"} : Finset String) := by
  have h7_mem : ("0010101" : String) ∈ allowedWordsFinset 7 := by decide
  have h7 :
      (allowedWordsFinset 7).filter (fun w => prefixOf w 7 = ("0010101" : String)) =
        ({("0010101" : String)} : Finset String) :=
    filter_prefix_exact h7_mem
  have h8 :
      (allowedWordsFinset 8).filter (fun w => prefixOf w 7 = ("0010101" : String)) =
        ({("00101010" : String)} : Finset String) := by
    rw [filter_prefix_step (m := 7) (n := 6) (x := ("0010101" : String)) (by decide), h7]
    decide
  have h9 :
      (allowedWordsFinset 9).filter (fun w => prefixOf w 7 = ("0010101" : String)) =
        ({("001010100" : String), "001010101"} : Finset String) := by
    rw [filter_prefix_step (m := 7) (n := 7) (x := ("0010101" : String)) (by decide), h8]
    decide
  have h10 :
      (allowedWordsFinset 10).filter (fun w => prefixOf w 7 = ("0010101" : String)) =
        ({("0010101001" : String), "0010101010"} : Finset String) := by
    rw [filter_prefix_step (m := 7) (n := 8) (x := ("0010101" : String)) (by decide), h9]
    decide
  have h11 :
      (allowedWordsFinset 11).filter (fun w => prefixOf w 7 = ("0010101" : String)) =
        ({("00101010010" : String), "00101010100", "00101010101"} : Finset String) := by
    rw [filter_prefix_step (m := 7) (n := 9) (x := ("0010101" : String)) (by decide), h10]
    decide
  have h12 :
      (allowedWordsFinset 12).filter (fun w => prefixOf w 7 = ("0010101" : String)) =
        ({("001010100100" : String), "001010100101", "001010101001", "001010101010"} :
          Finset String) := by
    rw [filter_prefix_step (m := 7) (n := 10) (x := ("0010101" : String)) (by decide), h11]
    decide
  have h12_empty :
      (allowedWordsFinset 12).filter
          (fun w => prefixOf w 7 = ("0010101" : String) ∧ suffixFrom w (7 + 5) = ("" : String)) =
        ({("001010100100" : String), "001010100101", "001010101001", "001010101010"} :
          Finset String) := by
    rw [filter_pref_suf_empty (m := 7) (L := 12) (x := ("0010101" : String)) (by decide), h12]
  have h13 :
      (allowedWordsFinset 13).filter
          (fun w => prefixOf w 7 = ("0010101" : String) ∧ suffixFrom w (7 + 5) = ("0" : String)) =
        ({("0010101001010" : String), "0010101010010", "0010101010100"} : Finset String) := by
    calc
      (allowedWordsFinset 13).filter
          (fun w => prefixOf w 7 = ("0010101" : String) ∧ suffixFrom w (7 + 5) = ("0" : String)) =
            (((allowedWordsFinset 12).filter
                (fun w => prefixOf w 7 = ("0010101" : String) ∧ suffixFrom w (7 + 5) = ("" : String))).biUnion
              fun w => ((K5Data.extensions w).toFinset).filter
                (fun s => suffixFrom s (7 + 5) = ("0" : String))) := by
              simpa using (filter_pref_suf_step (m := 7) (n := 11) (x := ("0010101" : String))
                (u := ("" : String)) (c := '0') (hm := by decide) (hk := by decide))
      _ = ({("0010101001010" : String), "0010101010010", "0010101010100"} : Finset String) := by
            rw [h12_empty]
            decide
  have h14 :
      (allowedWordsFinset 14).filter
          (fun w => prefixOf w 7 = ("0010101" : String) ∧ suffixFrom w (7 + 5) = ("00" : String)) =
        ({("00101010010100" : String), "00101010100100"} : Finset String) := by
    calc
      (allowedWordsFinset 14).filter
          (fun w => prefixOf w 7 = ("0010101" : String) ∧ suffixFrom w (7 + 5) = ("00" : String)) =
            (((allowedWordsFinset 13).filter
                (fun w => prefixOf w 7 = ("0010101" : String) ∧ suffixFrom w (7 + 5) = ("0" : String))).biUnion
              fun w => ((K5Data.extensions w).toFinset).filter
                (fun s => suffixFrom s (7 + 5) = ("00" : String))) := by
              simpa using (filter_pref_suf_step (m := 7) (n := 12) (x := ("0010101" : String))
                (u := ("0" : String)) (c := '0') (hm := by decide) (hk := by decide))
      _ = ({("00101010010100" : String), "00101010100100"} : Finset String) := by
            rw [h13]
            decide
  have h15 :
      (allowedWordsFinset 15).filter
          (fun w => prefixOf w 7 = ("0010101" : String) ∧ suffixFrom w (7 + 5) = ("001" : String)) =
        ({("001010100101001" : String), "001010101001001"} : Finset String) := by
    calc
      (allowedWordsFinset 15).filter
          (fun w => prefixOf w 7 = ("0010101" : String) ∧ suffixFrom w (7 + 5) = ("001" : String)) =
            (((allowedWordsFinset 14).filter
                (fun w => prefixOf w 7 = ("0010101" : String) ∧ suffixFrom w (7 + 5) = ("00" : String))).biUnion
              fun w => ((K5Data.extensions w).toFinset).filter
                (fun s => suffixFrom s (7 + 5) = ("001" : String))) := by
              simpa using (filter_pref_suf_step (m := 7) (n := 13) (x := ("0010101" : String))
                (u := ("00" : String)) (c := '1') (hm := by decide) (hk := by decide))
      _ = ({("001010100101001" : String), "001010101001001"} : Finset String) := by
            rw [h14]
            decide
  have h16 :
      (allowedWordsFinset 16).filter
          (fun w => prefixOf w 7 = ("0010101" : String) ∧ suffixFrom w (7 + 5) = ("0010" : String)) =
        ({("0010101001010010" : String), "0010101010010010"} : Finset String) := by
    calc
      (allowedWordsFinset 16).filter
          (fun w => prefixOf w 7 = ("0010101" : String) ∧ suffixFrom w (7 + 5) = ("0010" : String)) =
            (((allowedWordsFinset 15).filter
                (fun w => prefixOf w 7 = ("0010101" : String) ∧ suffixFrom w (7 + 5) = ("001" : String))).biUnion
              fun w => ((K5Data.extensions w).toFinset).filter
                (fun s => suffixFrom s (7 + 5) = ("0010" : String))) := by
              simpa using (filter_pref_suf_step (m := 7) (n := 14) (x := ("0010101" : String))
                (u := ("001" : String)) (c := '0') (hm := by decide) (hk := by decide))
      _ = ({("0010101001010010" : String), "0010101010010010"} : Finset String) := by
            rw [h15]
            decide
  have h17 :
      (allowedWordsFinset 17).filter
          (fun w => prefixOf w 7 = ("0010101" : String) ∧ suffixFrom w (7 + 5) = ("00101" : String)) =
        ({("00101010010100101" : String), "00101010100100101"} : Finset String) := by
    calc
      (allowedWordsFinset 17).filter
          (fun w => prefixOf w 7 = ("0010101" : String) ∧ suffixFrom w (7 + 5) = ("00101" : String)) =
            (((allowedWordsFinset 16).filter
                (fun w => prefixOf w 7 = ("0010101" : String) ∧ suffixFrom w (7 + 5) = ("0010" : String))).biUnion
              fun w => ((K5Data.extensions w).toFinset).filter
                (fun s => suffixFrom s (7 + 5) = ("00101" : String))) := by
              simpa using (filter_pref_suf_step (m := 7) (n := 15) (x := ("0010101" : String))
                (u := ("0010" : String)) (c := '1') (hm := by decide) (hk := by decide))
      _ = ({("00101010010100101" : String), "00101010100100101"} : Finset String) := by
            rw [h16]
            decide
  have h18 :
      (allowedWordsFinset 18).filter
          (fun w => prefixOf w 7 = ("0010101" : String) ∧ suffixFrom w (7 + 5) = ("001010" : String)) =
        ({("001010100101001010" : String), "001010101001001010"} : Finset String) := by
    calc
      (allowedWordsFinset 18).filter
          (fun w => prefixOf w 7 = ("0010101" : String) ∧ suffixFrom w (7 + 5) = ("001010" : String)) =
            (((allowedWordsFinset 17).filter
                (fun w => prefixOf w 7 = ("0010101" : String) ∧ suffixFrom w (7 + 5) = ("00101" : String))).biUnion
              fun w => ((K5Data.extensions w).toFinset).filter
                (fun s => suffixFrom s (7 + 5) = ("001010" : String))) := by
              simpa using (filter_pref_suf_step (m := 7) (n := 16) (x := ("0010101" : String))
                (u := ("00101" : String)) (c := '0') (hm := by decide) (hk := by decide))
      _ = ({("001010100101001010" : String), "001010101001001010"} : Finset String) := by
            rw [h17]
            decide
  have h19 :
      (allowedWordsFinset 19).filter
          (fun w => prefixOf w 7 = ("0010101" : String) ∧ suffixFrom w (7 + 5) = ("0010100" : String)) =
        ({("0010101001010010100" : String), "0010101010010010100"} : Finset String) := by
    calc
      (allowedWordsFinset 19).filter
          (fun w => prefixOf w 7 = ("0010101" : String) ∧ suffixFrom w (7 + 5) = ("0010100" : String)) =
            (((allowedWordsFinset 18).filter
                (fun w => prefixOf w 7 = ("0010101" : String) ∧ suffixFrom w (7 + 5) = ("001010" : String))).biUnion
              fun w => ((K5Data.extensions w).toFinset).filter
                (fun s => suffixFrom s (7 + 5) = ("0010100" : String))) := by
              simpa using (filter_pref_suf_step (m := 7) (n := 17) (x := ("0010101" : String))
                (u := ("001010" : String)) (c := '0') (hm := by decide) (hk := by decide))
      _ = ({("0010101001010010100" : String), "0010101010010010100"} : Finset String) := by
            rw [h18]
            decide
  exact h19

end Step4Sparse

end

end Model

end K5Bridge

end FiniteDependence.MIS
