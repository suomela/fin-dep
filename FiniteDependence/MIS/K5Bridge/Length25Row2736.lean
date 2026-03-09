import FiniteDependence.MIS.K5Bridge.Length25RowsCommon

namespace FiniteDependence.MIS

namespace K5Bridge

open MeasureTheory Set
open scoped ProbabilityTheory

namespace Model

open FiniteDependence.MIS.Model

noncomputable section

set_option maxRecDepth 1000000
set_option maxHeartbeats 20000000

private lemma is01_suf24 : Is01String suf24 :=
  is01_of_toList_eq (s := suf24)
    (cs := ['1', '0', '1', '0', '1', '0', '0', '1', '0', '1', '0', '1', '0', '1', '0', '0',
      '1', '0', '0', '1', '0', '1', '0', '0'])
    rfl <| by
      intro c hc
      simpa [or_assoc, or_left_comm, or_comm] using hc

private lemma is01_0 : Is01String ("0" : String) :=
  is01_of_toList_eq (s := ("0" : String)) (cs := ['0']) rfl <| by
    intro c hc
    exact Or.inl (by simpa using hc)

private lemma is01_wB : Is01String wB := by
  rw [wB_eq_suf24]
  exact is01_append is01_0 is01_suf24

set_option maxHeartbeats 400000 in
private lemma cylStr_succ_suf24_eq_cylStr_wB :
    cylStr (a := (1 : ℤ)) suf24 = cylStr (a := (0 : ℤ)) wB := by
  classical
  ext ω
  constructor
  · intro h
    have h1 : ω.1 1 = true := by
      simpa [K5Bridge.wordOfString, add_assoc, add_left_comm, add_comm] using
        (bit_eq_of_mem_cylStr (h := h) (i := ⟨0, by decide⟩))
    have h0 : ω.1 0 = false := by
      simpa [sub_eq_add_neg, add_assoc, add_left_comm, add_comm] using
        true_prev_false ω (i := (1 : ℤ)) h1
    have h0cyl : ω ∈ cylStr (a := (0 : ℤ)) ("0" : String) := by
      have hb : FiniteDependence.MIS.Model.block (0 : ℤ) ("0" : String).length ω =
          K5Bridge.wordOfString "0" := by
        funext i
        fin_cases i <;> (simp [FiniteDependence.MIS.Model.block, K5Bridge.wordOfString, h0] <;> decide)
      simpa [cylStr, FiniteDependence.MIS.Model.cyl] using hb
    have h0BS : blockString (a := (0 : ℤ)) 1 ω = ("0" : String) := by
      have := (mem_cylStr_iff_blockString_eq (a := (0 : ℤ)) ("0" : String) ω is01_0).1 h0cyl
      simpa using this
    have hSBS : blockString (a := (1 : ℤ)) 24 ω = suf24 := by
      have := (mem_cylStr_iff_blockString_eq (a := (1 : ℤ)) suf24 ω is01_suf24).1 h
      simpa [suf24_len] using this
    have hfull : blockString (a := (0 : ℤ)) 25 ω = wB := by
      calc
        blockString (a := (0 : ℤ)) 25 ω =
            (blockString (a := (0 : ℤ)) 1 ω) ++ blockString (a := (1 : ℤ)) 24 ω := by
              simpa using (blockString_add (ω := ω) (a := (0 : ℤ)) (m := 1) (n := 24))
        _ = ("0" : String) ++ suf24 := by simpa [h0BS, hSBS]
        _ = wB := by simpa [wB_eq_suf24] using rfl
    exact (mem_cylStr_iff_blockString_eq (a := (0 : ℤ)) wB ω is01_wB).2 (by simpa [wB_len] using hfull)
  · intro h
    have hBS : blockString (a := (0 : ℤ)) 25 ω = wB := by
      have := (mem_cylStr_iff_blockString_eq (a := (0 : ℤ)) wB ω is01_wB).1 h
      simpa [wB_len] using this
    have hdrop :
        String.ofList ((blockString (a := (0 : ℤ)) 25 ω).toList.drop 1) =
          blockString (a := (1 : ℤ)) 24 ω := by
      simpa using (ofList_drop_blockString_add (ω := ω) (a := (0 : ℤ)) (m := 1) (n := 24))
    have hBS' : blockString (a := (1 : ℤ)) 24 ω = String.ofList (wB.toList.drop 1) := by
      simpa [hBS] using hdrop.symm
    have hdropEq : String.ofList (wB.toList.drop 1) = suf24 := by decide
    have hBS'' : blockString (a := (1 : ℤ)) 24 ω = suf24 := by
      calc
        blockString (a := (1 : ℤ)) 24 ω = String.ofList (wB.toList.drop 1) := hBS'
        _ = suf24 := hdropEq
    exact
      (mem_cylStr_iff_blockString_eq (a := (1 : ℤ)) suf24 ω is01_suf24).2
        (by simpa [suf24_len] using hBS'')

theorem prob_row2736 (μ : Measure FiniteDependence.MIS.State) [IsProbabilityMeasure μ]
    (hstat : Stationary μ) :
    FiniteDependence.MIS.Model.prob μ (cylStr (a := 0) wB) =
      FiniteDependence.MIS.Model.prob μ (cylStr (a := 0) suf24) := by
  have hset : cylStr (a := (1 : ℤ)) suf24 = cylStr (a := (0 : ℤ)) wB := cylStr_succ_suf24_eq_cylStr_wB
  have hshift :
      FiniteDependence.MIS.Model.prob μ (cylStr (a := (1 : ℤ)) suf24) =
        FiniteDependence.MIS.Model.prob μ (cylStr (a := (0 : ℤ)) suf24) := by
    simpa using (Stationary.prob_cylStr_succ (μ := μ) hstat (a := (0 : ℤ)) (s := suf24))
  simpa [hset] using hshift

end

end Model

end K5Bridge

end FiniteDependence.MIS
