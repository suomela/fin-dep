import FiniteDependence.MIS.K5Bridge.Step2SparseFiltersCore

namespace FiniteDependence.MIS

namespace K5Bridge

namespace Model

noncomputable section

set_option maxRecDepth 1000000
set_option maxHeartbeats 20000000

namespace Step4Sparse

open Step2Sparse

theorem filter19_anchor_eq :
    (allowedWordsFinset (2 + 5 + 12)).filter
        (fun w => prefixOf w 2 = ("00" : String) ∧ suffixFrom w (2 + 5) = ("001010010100" : String)) =
      ({("0010101001010010100" : String)} : Finset String) := by
  have h2_mem : ("00" : String) ∈ allowedWordsFinset 2 := by decide
  have h2 :
      (allowedWordsFinset 2).filter (fun w => prefixOf w 2 = ("00" : String)) =
        ({("00" : String)} : Finset String) :=
    filter_prefix_exact h2_mem
  have h3 :
      (allowedWordsFinset 3).filter (fun w => prefixOf w 2 = ("00" : String)) =
        ({("001" : String)} : Finset String) := by
    rw [filter_prefix_step (m := 2) (n := 1) (x := ("00" : String)) (by decide), h2]
    decide
  have h4 :
      (allowedWordsFinset 4).filter (fun w => prefixOf w 2 = ("00" : String)) =
        ({("0010" : String)} : Finset String) := by
    rw [filter_prefix_step (m := 2) (n := 2) (x := ("00" : String)) (by decide), h3]
    decide
  have h5 :
      (allowedWordsFinset 5).filter (fun w => prefixOf w 2 = ("00" : String)) =
        ({("00100" : String), "00101"} : Finset String) := by
    rw [filter_prefix_step (m := 2) (n := 3) (x := ("00" : String)) (by decide), h4]
    decide
  have h6 :
      (allowedWordsFinset 6).filter (fun w => prefixOf w 2 = ("00" : String)) =
        ({("001001" : String), "001010"} : Finset String) := by
    rw [filter_prefix_step (m := 2) (n := 4) (x := ("00" : String)) (by decide), h5]
    decide
  have h7 :
      (allowedWordsFinset 7).filter (fun w => prefixOf w 2 = ("00" : String)) =
        ({("0010010" : String), "0010100", "0010101"} : Finset String) := by
    rw [filter_prefix_step (m := 2) (n := 5) (x := ("00" : String)) (by decide), h6]
    decide
  have h7_empty :
      (allowedWordsFinset 7).filter
          (fun w => prefixOf w 2 = ("00" : String) ∧ suffixFrom w (2 + 5) = ("" : String)) =
        ({("0010010" : String), "0010100", "0010101"} : Finset String) := by
    rw [filter_pref_suf_empty (m := 2) (L := 7) (x := ("00" : String)) (by decide), h7]
  have h8 :
      (allowedWordsFinset 8).filter
          (fun w => prefixOf w 2 = ("00" : String) ∧ suffixFrom w (2 + 5) = ("0" : String)) =
        ({("00100100" : String), "00101010"} : Finset String) := by
    calc
      (allowedWordsFinset 8).filter
          (fun w => prefixOf w 2 = ("00" : String) ∧ suffixFrom w (2 + 5) = ("0" : String)) =
            (((allowedWordsFinset 7).filter
                (fun w => prefixOf w 2 = ("00" : String) ∧ suffixFrom w (2 + 5) = ("" : String))).biUnion
              fun w => ((K5Data.extensions w).toFinset).filter
                (fun s => suffixFrom s (2 + 5) = ("0" : String))) := by
              simpa using (filter_pref_suf_step (m := 2) (n := 6) (x := ("00" : String))
                (u := ("" : String)) (c := '0') (hm := by decide) (hk := by decide))
      _ = ({("00100100" : String), "00101010"} : Finset String) := by
            rw [h7_empty]
            decide
  have h9 :
      (allowedWordsFinset 9).filter
          (fun w => prefixOf w 2 = ("00" : String) ∧ suffixFrom w (2 + 5) = ("00" : String)) =
        ({("001010100" : String)} : Finset String) := by
    calc
      (allowedWordsFinset 9).filter
          (fun w => prefixOf w 2 = ("00" : String) ∧ suffixFrom w (2 + 5) = ("00" : String)) =
            (((allowedWordsFinset 8).filter
                (fun w => prefixOf w 2 = ("00" : String) ∧ suffixFrom w (2 + 5) = ("0" : String))).biUnion
              fun w => ((K5Data.extensions w).toFinset).filter
                (fun s => suffixFrom s (2 + 5) = ("00" : String))) := by
              simpa using (filter_pref_suf_step (m := 2) (n := 7) (x := ("00" : String))
                (u := ("0" : String)) (c := '0') (hm := by decide) (hk := by decide))
      _ = ({("001010100" : String)} : Finset String) := by
            rw [h8]
            decide
  have h10 :
      (allowedWordsFinset 10).filter
          (fun w => prefixOf w 2 = ("00" : String) ∧ suffixFrom w (2 + 5) = ("001" : String)) =
        ({("0010101001" : String)} : Finset String) := by
    calc
      (allowedWordsFinset 10).filter
          (fun w => prefixOf w 2 = ("00" : String) ∧ suffixFrom w (2 + 5) = ("001" : String)) =
            (((allowedWordsFinset 9).filter
                (fun w => prefixOf w 2 = ("00" : String) ∧ suffixFrom w (2 + 5) = ("00" : String))).biUnion
              fun w => ((K5Data.extensions w).toFinset).filter
                (fun s => suffixFrom s (2 + 5) = ("001" : String))) := by
              simpa using (filter_pref_suf_step (m := 2) (n := 8) (x := ("00" : String))
                (u := ("00" : String)) (c := '1') (hm := by decide) (hk := by decide))
      _ = ({("0010101001" : String)} : Finset String) := by
            rw [h9]
            decide
  have h11 :
      (allowedWordsFinset 11).filter
          (fun w => prefixOf w 2 = ("00" : String) ∧ suffixFrom w (2 + 5) = ("0010" : String)) =
        ({("00101010010" : String)} : Finset String) := by
    calc
      (allowedWordsFinset 11).filter
          (fun w => prefixOf w 2 = ("00" : String) ∧ suffixFrom w (2 + 5) = ("0010" : String)) =
            (((allowedWordsFinset 10).filter
                (fun w => prefixOf w 2 = ("00" : String) ∧ suffixFrom w (2 + 5) = ("001" : String))).biUnion
              fun w => ((K5Data.extensions w).toFinset).filter
                (fun s => suffixFrom s (2 + 5) = ("0010" : String))) := by
              simpa using (filter_pref_suf_step (m := 2) (n := 9) (x := ("00" : String))
                (u := ("001" : String)) (c := '0') (hm := by decide) (hk := by decide))
      _ = ({("00101010010" : String)} : Finset String) := by
            rw [h10]
            decide
  have h12 :
      (allowedWordsFinset 12).filter
          (fun w => prefixOf w 2 = ("00" : String) ∧ suffixFrom w (2 + 5) = ("00101" : String)) =
        ({("001010100101" : String)} : Finset String) := by
    calc
      (allowedWordsFinset 12).filter
          (fun w => prefixOf w 2 = ("00" : String) ∧ suffixFrom w (2 + 5) = ("00101" : String)) =
            (((allowedWordsFinset 11).filter
                (fun w => prefixOf w 2 = ("00" : String) ∧ suffixFrom w (2 + 5) = ("0010" : String))).biUnion
              fun w => ((K5Data.extensions w).toFinset).filter
                (fun s => suffixFrom s (2 + 5) = ("00101" : String))) := by
              simpa using (filter_pref_suf_step (m := 2) (n := 10) (x := ("00" : String))
                (u := ("0010" : String)) (c := '1') (hm := by decide) (hk := by decide))
      _ = ({("001010100101" : String)} : Finset String) := by
            rw [h11]
            decide
  have h13 :
      (allowedWordsFinset 13).filter
          (fun w => prefixOf w 2 = ("00" : String) ∧ suffixFrom w (2 + 5) = ("001010" : String)) =
        ({("0010101001010" : String)} : Finset String) := by
    calc
      (allowedWordsFinset 13).filter
          (fun w => prefixOf w 2 = ("00" : String) ∧ suffixFrom w (2 + 5) = ("001010" : String)) =
            (((allowedWordsFinset 12).filter
                (fun w => prefixOf w 2 = ("00" : String) ∧ suffixFrom w (2 + 5) = ("00101" : String))).biUnion
              fun w => ((K5Data.extensions w).toFinset).filter
                (fun s => suffixFrom s (2 + 5) = ("001010" : String))) := by
              simpa using (filter_pref_suf_step (m := 2) (n := 11) (x := ("00" : String))
                (u := ("00101" : String)) (c := '0') (hm := by decide) (hk := by decide))
      _ = ({("0010101001010" : String)} : Finset String) := by
            rw [h12]
            decide
  have h14 :
      (allowedWordsFinset 14).filter
          (fun w => prefixOf w 2 = ("00" : String) ∧ suffixFrom w (2 + 5) = ("0010100" : String)) =
        ({("00101010010100" : String)} : Finset String) := by
    calc
      (allowedWordsFinset 14).filter
          (fun w => prefixOf w 2 = ("00" : String) ∧ suffixFrom w (2 + 5) = ("0010100" : String)) =
            (((allowedWordsFinset 13).filter
                (fun w => prefixOf w 2 = ("00" : String) ∧ suffixFrom w (2 + 5) = ("001010" : String))).biUnion
              fun w => ((K5Data.extensions w).toFinset).filter
                (fun s => suffixFrom s (2 + 5) = ("0010100" : String))) := by
              simpa using (filter_pref_suf_step (m := 2) (n := 12) (x := ("00" : String))
                (u := ("001010" : String)) (c := '0') (hm := by decide) (hk := by decide))
      _ = ({("00101010010100" : String)} : Finset String) := by
            rw [h13]
            decide
  have h15 :
      (allowedWordsFinset 15).filter
          (fun w => prefixOf w 2 = ("00" : String) ∧ suffixFrom w (2 + 5) = ("00101001" : String)) =
        ({("001010100101001" : String)} : Finset String) := by
    calc
      (allowedWordsFinset 15).filter
          (fun w => prefixOf w 2 = ("00" : String) ∧ suffixFrom w (2 + 5) = ("00101001" : String)) =
            (((allowedWordsFinset 14).filter
                (fun w => prefixOf w 2 = ("00" : String) ∧ suffixFrom w (2 + 5) = ("0010100" : String))).biUnion
              fun w => ((K5Data.extensions w).toFinset).filter
                (fun s => suffixFrom s (2 + 5) = ("00101001" : String))) := by
              simpa using (filter_pref_suf_step (m := 2) (n := 13) (x := ("00" : String))
                (u := ("0010100" : String)) (c := '1') (hm := by decide) (hk := by decide))
      _ = ({("001010100101001" : String)} : Finset String) := by
            rw [h14]
            decide
  have h16 :
      (allowedWordsFinset 16).filter
          (fun w => prefixOf w 2 = ("00" : String) ∧ suffixFrom w (2 + 5) = ("001010010" : String)) =
        ({("0010101001010010" : String)} : Finset String) := by
    calc
      (allowedWordsFinset 16).filter
          (fun w => prefixOf w 2 = ("00" : String) ∧ suffixFrom w (2 + 5) = ("001010010" : String)) =
            (((allowedWordsFinset 15).filter
                (fun w => prefixOf w 2 = ("00" : String) ∧ suffixFrom w (2 + 5) = ("00101001" : String))).biUnion
              fun w => ((K5Data.extensions w).toFinset).filter
                (fun s => suffixFrom s (2 + 5) = ("001010010" : String))) := by
              simpa using (filter_pref_suf_step (m := 2) (n := 14) (x := ("00" : String))
                (u := ("00101001" : String)) (c := '0') (hm := by decide) (hk := by decide))
      _ = ({("0010101001010010" : String)} : Finset String) := by
            rw [h15]
            decide
  have h17 :
      (allowedWordsFinset 17).filter
          (fun w => prefixOf w 2 = ("00" : String) ∧ suffixFrom w (2 + 5) = ("0010100101" : String)) =
        ({("00101010010100101" : String)} : Finset String) := by
    calc
      (allowedWordsFinset 17).filter
          (fun w => prefixOf w 2 = ("00" : String) ∧ suffixFrom w (2 + 5) = ("0010100101" : String)) =
            (((allowedWordsFinset 16).filter
                (fun w => prefixOf w 2 = ("00" : String) ∧ suffixFrom w (2 + 5) = ("001010010" : String))).biUnion
              fun w => ((K5Data.extensions w).toFinset).filter
                (fun s => suffixFrom s (2 + 5) = ("0010100101" : String))) := by
              simpa using (filter_pref_suf_step (m := 2) (n := 15) (x := ("00" : String))
                (u := ("001010010" : String)) (c := '1') (hm := by decide) (hk := by decide))
      _ = ({("00101010010100101" : String)} : Finset String) := by
            rw [h16]
            decide
  have h18 :
      (allowedWordsFinset 18).filter
          (fun w => prefixOf w 2 = ("00" : String) ∧ suffixFrom w (2 + 5) = ("00101001010" : String)) =
        ({("001010100101001010" : String)} : Finset String) := by
    calc
      (allowedWordsFinset 18).filter
          (fun w => prefixOf w 2 = ("00" : String) ∧ suffixFrom w (2 + 5) = ("00101001010" : String)) =
            (((allowedWordsFinset 17).filter
                (fun w => prefixOf w 2 = ("00" : String) ∧ suffixFrom w (2 + 5) = ("0010100101" : String))).biUnion
              fun w => ((K5Data.extensions w).toFinset).filter
                (fun s => suffixFrom s (2 + 5) = ("00101001010" : String))) := by
              simpa using (filter_pref_suf_step (m := 2) (n := 16) (x := ("00" : String))
                (u := ("0010100101" : String)) (c := '0') (hm := by decide) (hk := by decide))
      _ = ({("001010100101001010" : String)} : Finset String) := by
            rw [h17]
            decide
  have h19 :
      (allowedWordsFinset 19).filter
          (fun w => prefixOf w 2 = ("00" : String) ∧ suffixFrom w (2 + 5) = ("001010010100" : String)) =
        ({("0010101001010010100" : String)} : Finset String) := by
    calc
      (allowedWordsFinset 19).filter
          (fun w => prefixOf w 2 = ("00" : String) ∧ suffixFrom w (2 + 5) = ("001010010100" : String)) =
            (((allowedWordsFinset 18).filter
                (fun w => prefixOf w 2 = ("00" : String) ∧ suffixFrom w (2 + 5) = ("00101001010" : String))).biUnion
              fun w => ((K5Data.extensions w).toFinset).filter
                (fun s => suffixFrom s (2 + 5) = ("001010010100" : String))) := by
              simpa using (filter_pref_suf_step (m := 2) (n := 17) (x := ("00" : String))
                (u := ("00101001010" : String)) (c := '0') (hm := by decide) (hk := by decide))
      _ = ({("0010101001010010100" : String)} : Finset String) := by
            rw [h18]
            decide
  exact h19

end Step4Sparse

end

end Model

end K5Bridge

end FiniteDependence.MIS
