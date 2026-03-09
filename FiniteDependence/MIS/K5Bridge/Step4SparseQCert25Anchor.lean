import FiniteDependence.MIS.K5Bridge.Step2SparseFiltersCore

namespace FiniteDependence.MIS

namespace K5Bridge

namespace Model

noncomputable section

set_option maxRecDepth 1000000
set_option maxHeartbeats 20000000

namespace Step4Sparse

open Step2Sparse

theorem filter25_anchor_eq :
    (allowedWordsFinset (8 + 5 + 12)).filter
        (fun w => prefixOf w 8 = ("01010100" : String) ∧ suffixFrom w (8 + 5) = ("001010010100" : String)) =
      ({("0101010010101001010010100" : String)} : Finset String) := by
  have h13 :
      (allowedWordsFinset 13).filter (fun w => prefixOf w 8 = ("01010100" : String)) =
        ({("0101010010010" : String), "0101010010100", "0101010010101"} : Finset String) := by
    decide
  have h14 :
      (allowedWordsFinset 14).filter
          (fun w => prefixOf w 8 = ("01010100" : String) ∧ suffixFrom w (8 + 5) = ("0" : String)) =
        ({("01010100100100" : String), "01010100101010"} : Finset String) := by
    calc
      (allowedWordsFinset 14).filter
          (fun w => prefixOf w 8 = ("01010100" : String) ∧ suffixFrom w (8 + 5) = ("0" : String)) =
            (((allowedWordsFinset 13).filter (fun w => prefixOf w 8 = ("01010100" : String))).biUnion
              fun w => ((K5Data.extensions w).toFinset).filter
                (fun s => suffixFrom s (8 + 5) = ("0" : String))) := by
              simpa using (filter_pref_suf_step (m := 8) (n := 12) (x := ("01010100" : String))
                (u := ("" : String)) (c := '0') (hm := by decide) (hk := by decide))
      _ = ({("01010100100100" : String), "01010100101010"} : Finset String) := by
            rw [h13]
            decide
  have h15 :
      (allowedWordsFinset 15).filter
          (fun w => prefixOf w 8 = ("01010100" : String) ∧ suffixFrom w (8 + 5) = ("00" : String)) =
        ({("010101001010100" : String)} : Finset String) := by
    calc
      (allowedWordsFinset 15).filter
          (fun w => prefixOf w 8 = ("01010100" : String) ∧ suffixFrom w (8 + 5) = ("00" : String)) =
            (((allowedWordsFinset 14).filter
                (fun w => prefixOf w 8 = ("01010100" : String) ∧ suffixFrom w (8 + 5) = ("0" : String))).biUnion
              fun w => ((K5Data.extensions w).toFinset).filter
                (fun s => suffixFrom s (8 + 5) = ("00" : String))) := by
              simpa using (filter_pref_suf_step (m := 8) (n := 13) (x := ("01010100" : String))
                (u := ("0" : String)) (c := '0') (hm := by decide) (hk := by decide))
      _ = ({("010101001010100" : String)} : Finset String) := by
            rw [h14]
            decide
  have h16 :
      (allowedWordsFinset 16).filter
          (fun w => prefixOf w 8 = ("01010100" : String) ∧ suffixFrom w (8 + 5) = ("001" : String)) =
        ({("0101010010101001" : String)} : Finset String) := by
    calc
      (allowedWordsFinset 16).filter
          (fun w => prefixOf w 8 = ("01010100" : String) ∧ suffixFrom w (8 + 5) = ("001" : String)) =
            (((allowedWordsFinset 15).filter
                (fun w => prefixOf w 8 = ("01010100" : String) ∧ suffixFrom w (8 + 5) = ("00" : String))).biUnion
              fun w => ((K5Data.extensions w).toFinset).filter
                (fun s => suffixFrom s (8 + 5) = ("001" : String))) := by
              simpa using (filter_pref_suf_step (m := 8) (n := 14) (x := ("01010100" : String))
                (u := ("00" : String)) (c := '1') (hm := by decide) (hk := by decide))
      _ = ({("0101010010101001" : String)} : Finset String) := by
            rw [h15]
            decide
  have h17 :
      (allowedWordsFinset 17).filter
          (fun w => prefixOf w 8 = ("01010100" : String) ∧ suffixFrom w (8 + 5) = ("0010" : String)) =
        ({("01010100101010010" : String)} : Finset String) := by
    calc
      (allowedWordsFinset 17).filter
          (fun w => prefixOf w 8 = ("01010100" : String) ∧ suffixFrom w (8 + 5) = ("0010" : String)) =
            (((allowedWordsFinset 16).filter
                (fun w => prefixOf w 8 = ("01010100" : String) ∧ suffixFrom w (8 + 5) = ("001" : String))).biUnion
              fun w => ((K5Data.extensions w).toFinset).filter
                (fun s => suffixFrom s (8 + 5) = ("0010" : String))) := by
              simpa using (filter_pref_suf_step (m := 8) (n := 15) (x := ("01010100" : String))
                (u := ("001" : String)) (c := '0') (hm := by decide) (hk := by decide))
      _ = ({("01010100101010010" : String)} : Finset String) := by
            rw [h16]
            decide
  have h18 :
      (allowedWordsFinset 18).filter
          (fun w => prefixOf w 8 = ("01010100" : String) ∧ suffixFrom w (8 + 5) = ("00101" : String)) =
        ({("010101001010100101" : String)} : Finset String) := by
    calc
      (allowedWordsFinset 18).filter
          (fun w => prefixOf w 8 = ("01010100" : String) ∧ suffixFrom w (8 + 5) = ("00101" : String)) =
            (((allowedWordsFinset 17).filter
                (fun w => prefixOf w 8 = ("01010100" : String) ∧ suffixFrom w (8 + 5) = ("0010" : String))).biUnion
              fun w => ((K5Data.extensions w).toFinset).filter
                (fun s => suffixFrom s (8 + 5) = ("00101" : String))) := by
              simpa using (filter_pref_suf_step (m := 8) (n := 16) (x := ("01010100" : String))
                (u := ("0010" : String)) (c := '1') (hm := by decide) (hk := by decide))
      _ = ({("010101001010100101" : String)} : Finset String) := by
            rw [h17]
            decide
  have h19 :
      (allowedWordsFinset 19).filter
          (fun w => prefixOf w 8 = ("01010100" : String) ∧ suffixFrom w (8 + 5) = ("001010" : String)) =
        ({("0101010010101001010" : String)} : Finset String) := by
    calc
      (allowedWordsFinset 19).filter
          (fun w => prefixOf w 8 = ("01010100" : String) ∧ suffixFrom w (8 + 5) = ("001010" : String)) =
            (((allowedWordsFinset 18).filter
                (fun w => prefixOf w 8 = ("01010100" : String) ∧ suffixFrom w (8 + 5) = ("00101" : String))).biUnion
              fun w => ((K5Data.extensions w).toFinset).filter
                (fun s => suffixFrom s (8 + 5) = ("001010" : String))) := by
              simpa using (filter_pref_suf_step (m := 8) (n := 17) (x := ("01010100" : String))
                (u := ("00101" : String)) (c := '0') (hm := by decide) (hk := by decide))
      _ = ({("0101010010101001010" : String)} : Finset String) := by
            rw [h18]
            decide
  have h20 :
      (allowedWordsFinset 20).filter
          (fun w => prefixOf w 8 = ("01010100" : String) ∧ suffixFrom w (8 + 5) = ("0010100" : String)) =
        ({("01010100101010010100" : String)} : Finset String) := by
    calc
      (allowedWordsFinset 20).filter
          (fun w => prefixOf w 8 = ("01010100" : String) ∧ suffixFrom w (8 + 5) = ("0010100" : String)) =
            (((allowedWordsFinset 19).filter
                (fun w => prefixOf w 8 = ("01010100" : String) ∧ suffixFrom w (8 + 5) = ("001010" : String))).biUnion
              fun w => ((K5Data.extensions w).toFinset).filter
                (fun s => suffixFrom s (8 + 5) = ("0010100" : String))) := by
              simpa using (filter_pref_suf_step (m := 8) (n := 18) (x := ("01010100" : String))
                (u := ("001010" : String)) (c := '0') (hm := by decide) (hk := by decide))
      _ = ({("01010100101010010100" : String)} : Finset String) := by
            rw [h19]
            decide
  have h21 :
      (allowedWordsFinset 21).filter
          (fun w => prefixOf w 8 = ("01010100" : String) ∧ suffixFrom w (8 + 5) = ("00101001" : String)) =
        ({("010101001010100101001" : String)} : Finset String) := by
    calc
      (allowedWordsFinset 21).filter
          (fun w => prefixOf w 8 = ("01010100" : String) ∧ suffixFrom w (8 + 5) = ("00101001" : String)) =
            (((allowedWordsFinset 20).filter
                (fun w => prefixOf w 8 = ("01010100" : String) ∧ suffixFrom w (8 + 5) = ("0010100" : String))).biUnion
              fun w => ((K5Data.extensions w).toFinset).filter
                (fun s => suffixFrom s (8 + 5) = ("00101001" : String))) := by
              simpa using (filter_pref_suf_step (m := 8) (n := 19) (x := ("01010100" : String))
                (u := ("0010100" : String)) (c := '1') (hm := by decide) (hk := by decide))
      _ = ({("010101001010100101001" : String)} : Finset String) := by
            rw [h20]
            decide
  have h22 :
      (allowedWordsFinset 22).filter
          (fun w => prefixOf w 8 = ("01010100" : String) ∧ suffixFrom w (8 + 5) = ("001010010" : String)) =
        ({("0101010010101001010010" : String)} : Finset String) := by
    calc
      (allowedWordsFinset 22).filter
          (fun w => prefixOf w 8 = ("01010100" : String) ∧ suffixFrom w (8 + 5) = ("001010010" : String)) =
            (((allowedWordsFinset 21).filter
                (fun w => prefixOf w 8 = ("01010100" : String) ∧ suffixFrom w (8 + 5) = ("00101001" : String))).biUnion
              fun w => ((K5Data.extensions w).toFinset).filter
                (fun s => suffixFrom s (8 + 5) = ("001010010" : String))) := by
              simpa using (filter_pref_suf_step (m := 8) (n := 20) (x := ("01010100" : String))
                (u := ("00101001" : String)) (c := '0') (hm := by decide) (hk := by decide))
      _ = ({("0101010010101001010010" : String)} : Finset String) := by
            rw [h21]
            decide
  have h23 :
      (allowedWordsFinset 23).filter
          (fun w => prefixOf w 8 = ("01010100" : String) ∧ suffixFrom w (8 + 5) = ("0010100101" : String)) =
        ({("01010100101010010100101" : String)} : Finset String) := by
    calc
      (allowedWordsFinset 23).filter
          (fun w => prefixOf w 8 = ("01010100" : String) ∧ suffixFrom w (8 + 5) = ("0010100101" : String)) =
            (((allowedWordsFinset 22).filter
                (fun w => prefixOf w 8 = ("01010100" : String) ∧ suffixFrom w (8 + 5) = ("001010010" : String))).biUnion
              fun w => ((K5Data.extensions w).toFinset).filter
                (fun s => suffixFrom s (8 + 5) = ("0010100101" : String))) := by
              simpa using (filter_pref_suf_step (m := 8) (n := 21) (x := ("01010100" : String))
                (u := ("001010010" : String)) (c := '1') (hm := by decide) (hk := by decide))
      _ = ({("01010100101010010100101" : String)} : Finset String) := by
            rw [h22]
            decide
  have h24 :
      (allowedWordsFinset 24).filter
          (fun w => prefixOf w 8 = ("01010100" : String) ∧ suffixFrom w (8 + 5) = ("00101001010" : String)) =
        ({("010101001010100101001010" : String)} : Finset String) := by
    calc
      (allowedWordsFinset 24).filter
          (fun w => prefixOf w 8 = ("01010100" : String) ∧ suffixFrom w (8 + 5) = ("00101001010" : String)) =
            (((allowedWordsFinset 23).filter
                (fun w => prefixOf w 8 = ("01010100" : String) ∧ suffixFrom w (8 + 5) = ("0010100101" : String))).biUnion
              fun w => ((K5Data.extensions w).toFinset).filter
                (fun s => suffixFrom s (8 + 5) = ("00101001010" : String))) := by
              simpa using (filter_pref_suf_step (m := 8) (n := 22) (x := ("01010100" : String))
                (u := ("0010100101" : String)) (c := '0') (hm := by decide) (hk := by decide))
      _ = ({("010101001010100101001010" : String)} : Finset String) := by
            rw [h23]
            decide
  have h25 :
      (allowedWordsFinset 25).filter
          (fun w => prefixOf w 8 = ("01010100" : String) ∧ suffixFrom w (8 + 5) = ("001010010100" : String)) =
        ({("0101010010101001010010100" : String)} : Finset String) := by
    calc
      (allowedWordsFinset 25).filter
          (fun w => prefixOf w 8 = ("01010100" : String) ∧ suffixFrom w (8 + 5) = ("001010010100" : String)) =
            (((allowedWordsFinset 24).filter
                (fun w => prefixOf w 8 = ("01010100" : String) ∧ suffixFrom w (8 + 5) = ("00101001010" : String))).biUnion
              fun w => ((K5Data.extensions w).toFinset).filter
                (fun s => suffixFrom s (8 + 5) = ("001010010100" : String))) := by
              simpa using (filter_pref_suf_step (m := 8) (n := 23) (x := ("01010100" : String))
                (u := ("00101001010" : String)) (c := '0') (hm := by decide) (hk := by decide))
      _ = ({("0101010010101001010010100" : String)} : Finset String) := by
            rw [h24]
            decide
  exact h25

end Step4Sparse

end

end Model

end K5Bridge

end FiniteDependence.MIS
