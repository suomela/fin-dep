import FiniteDependence.MIS.K5Bridge.Step2SparseFiltersCore

namespace FiniteDependence.MIS

namespace K5Bridge

namespace Model

noncomputable section

set_option maxRecDepth 1000000
set_option maxHeartbeats 20000000

namespace Step4Sparse

open Step2Sparse

theorem filter25_edge_eq :
    (allowedWordsFinset (13 + 5 + 7)).filter
        (fun w => prefixOf w 13 = ("0101010010101" : String) ∧ suffixFrom w (13 + 5) = ("0010100" : String)) =
      ({("0101010010101001010010100" : String), "0101010010101010010010100"} : Finset String) := by
  have h18 :
      (allowedWordsFinset 18).filter (fun w => prefixOf w 13 = ("0101010010101" : String)) =
        ({("010101001010100100" : String), "010101001010100101", "010101001010101001",
          "010101001010101010"} : Finset String) := by
    decide
  have h19 :
      (allowedWordsFinset 19).filter
          (fun w => prefixOf w 13 = ("0101010010101" : String) ∧ suffixFrom w (13 + 5) = ("0" : String)) =
        ({("0101010010101001010" : String), "0101010010101010010", "0101010010101010100"} : Finset String) := by
    calc
      (allowedWordsFinset 19).filter
          (fun w => prefixOf w 13 = ("0101010010101" : String) ∧ suffixFrom w (13 + 5) = ("0" : String)) =
            (((allowedWordsFinset 18).filter (fun w => prefixOf w 13 = ("0101010010101" : String))).biUnion
              fun w => ((K5Data.extensions w).toFinset).filter
                (fun s => suffixFrom s (13 + 5) = ("0" : String))) := by
              simpa using (filter_pref_suf_step (m := 13) (n := 17) (x := ("0101010010101" : String))
                (u := ("" : String)) (c := '0') (hm := by decide) (hk := by decide))
      _ = ({("0101010010101001010" : String), "0101010010101010010", "0101010010101010100"} : Finset String) := by
            rw [h18]
            decide
  have h20 :
      (allowedWordsFinset 20).filter
          (fun w => prefixOf w 13 = ("0101010010101" : String) ∧ suffixFrom w (13 + 5) = ("00" : String)) =
        ({("01010100101010010100" : String), "01010100101010100100"} : Finset String) := by
    calc
      (allowedWordsFinset 20).filter
          (fun w => prefixOf w 13 = ("0101010010101" : String) ∧ suffixFrom w (13 + 5) = ("00" : String)) =
            (((allowedWordsFinset 19).filter
                (fun w => prefixOf w 13 = ("0101010010101" : String) ∧ suffixFrom w (13 + 5) = ("0" : String))).biUnion
              fun w => ((K5Data.extensions w).toFinset).filter
                (fun s => suffixFrom s (13 + 5) = ("00" : String))) := by
              simpa using (filter_pref_suf_step (m := 13) (n := 18) (x := ("0101010010101" : String))
                (u := ("0" : String)) (c := '0') (hm := by decide) (hk := by decide))
      _ = ({("01010100101010010100" : String), "01010100101010100100"} : Finset String) := by
            rw [h19]
            decide
  have h21 :
      (allowedWordsFinset 21).filter
          (fun w => prefixOf w 13 = ("0101010010101" : String) ∧ suffixFrom w (13 + 5) = ("001" : String)) =
        ({("010101001010100101001" : String), "010101001010101001001"} : Finset String) := by
    calc
      (allowedWordsFinset 21).filter
          (fun w => prefixOf w 13 = ("0101010010101" : String) ∧ suffixFrom w (13 + 5) = ("001" : String)) =
            (((allowedWordsFinset 20).filter
                (fun w => prefixOf w 13 = ("0101010010101" : String) ∧ suffixFrom w (13 + 5) = ("00" : String))).biUnion
              fun w => ((K5Data.extensions w).toFinset).filter
                (fun s => suffixFrom s (13 + 5) = ("001" : String))) := by
              simpa using (filter_pref_suf_step (m := 13) (n := 19) (x := ("0101010010101" : String))
                (u := ("00" : String)) (c := '1') (hm := by decide) (hk := by decide))
      _ = ({("010101001010100101001" : String), "010101001010101001001"} : Finset String) := by
            rw [h20]
            decide
  have h22 :
      (allowedWordsFinset 22).filter
          (fun w => prefixOf w 13 = ("0101010010101" : String) ∧ suffixFrom w (13 + 5) = ("0010" : String)) =
        ({("0101010010101001010010" : String), "0101010010101010010010"} : Finset String) := by
    calc
      (allowedWordsFinset 22).filter
          (fun w => prefixOf w 13 = ("0101010010101" : String) ∧ suffixFrom w (13 + 5) = ("0010" : String)) =
            (((allowedWordsFinset 21).filter
                (fun w => prefixOf w 13 = ("0101010010101" : String) ∧ suffixFrom w (13 + 5) = ("001" : String))).biUnion
              fun w => ((K5Data.extensions w).toFinset).filter
                (fun s => suffixFrom s (13 + 5) = ("0010" : String))) := by
              simpa using (filter_pref_suf_step (m := 13) (n := 20) (x := ("0101010010101" : String))
                (u := ("001" : String)) (c := '0') (hm := by decide) (hk := by decide))
      _ = ({("0101010010101001010010" : String), "0101010010101010010010"} : Finset String) := by
            rw [h21]
            decide
  have h23 :
      (allowedWordsFinset 23).filter
          (fun w => prefixOf w 13 = ("0101010010101" : String) ∧ suffixFrom w (13 + 5) = ("00101" : String)) =
        ({("01010100101010010100101" : String), "01010100101010100100101"} : Finset String) := by
    calc
      (allowedWordsFinset 23).filter
          (fun w => prefixOf w 13 = ("0101010010101" : String) ∧ suffixFrom w (13 + 5) = ("00101" : String)) =
            (((allowedWordsFinset 22).filter
                (fun w => prefixOf w 13 = ("0101010010101" : String) ∧ suffixFrom w (13 + 5) = ("0010" : String))).biUnion
              fun w => ((K5Data.extensions w).toFinset).filter
                (fun s => suffixFrom s (13 + 5) = ("00101" : String))) := by
              simpa using (filter_pref_suf_step (m := 13) (n := 21) (x := ("0101010010101" : String))
                (u := ("0010" : String)) (c := '1') (hm := by decide) (hk := by decide))
      _ = ({("01010100101010010100101" : String), "01010100101010100100101"} : Finset String) := by
            rw [h22]
            decide
  have h24 :
      (allowedWordsFinset 24).filter
          (fun w => prefixOf w 13 = ("0101010010101" : String) ∧ suffixFrom w (13 + 5) = ("001010" : String)) =
        ({("010101001010100101001010" : String), "010101001010101001001010"} : Finset String) := by
    calc
      (allowedWordsFinset 24).filter
          (fun w => prefixOf w 13 = ("0101010010101" : String) ∧ suffixFrom w (13 + 5) = ("001010" : String)) =
            (((allowedWordsFinset 23).filter
                (fun w => prefixOf w 13 = ("0101010010101" : String) ∧ suffixFrom w (13 + 5) = ("00101" : String))).biUnion
              fun w => ((K5Data.extensions w).toFinset).filter
                (fun s => suffixFrom s (13 + 5) = ("001010" : String))) := by
              simpa using (filter_pref_suf_step (m := 13) (n := 22) (x := ("0101010010101" : String))
                (u := ("00101" : String)) (c := '0') (hm := by decide) (hk := by decide))
      _ = ({("010101001010100101001010" : String), "010101001010101001001010"} : Finset String) := by
            rw [h23]
            decide
  have h25 :
      (allowedWordsFinset 25).filter
          (fun w => prefixOf w 13 = ("0101010010101" : String) ∧ suffixFrom w (13 + 5) = ("0010100" : String)) =
        ({("0101010010101001010010100" : String), "0101010010101010010010100"} : Finset String) := by
    calc
      (allowedWordsFinset 25).filter
          (fun w => prefixOf w 13 = ("0101010010101" : String) ∧ suffixFrom w (13 + 5) = ("0010100" : String)) =
            (((allowedWordsFinset 24).filter
                (fun w => prefixOf w 13 = ("0101010010101" : String) ∧ suffixFrom w (13 + 5) = ("001010" : String))).biUnion
              fun w => ((K5Data.extensions w).toFinset).filter
                (fun s => suffixFrom s (13 + 5) = ("0010100" : String))) := by
              simpa using (filter_pref_suf_step (m := 13) (n := 23) (x := ("0101010010101" : String))
                (u := ("001010" : String)) (c := '0') (hm := by decide) (hk := by decide))
      _ = ({("0101010010101001010010100" : String), "0101010010101010010010100"} : Finset String) := by
            rw [h24]
            decide
  exact h25

end Step4Sparse

end

end Model

end K5Bridge

end FiniteDependence.MIS
