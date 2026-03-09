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

private lemma is01_suf15 : Is01String suf15 :=
  is01_of_toList_eq (s := suf15)
    (cs := ['1', '0', '1', '0', '1', '0', '0', '1', '0', '0', '1', '0', '1', '0', '0'])
    rfl <| by
      intro c hc
      simpa [or_assoc, or_left_comm, or_comm] using hc

private lemma is01_00100 : Is01String ("00100" : String) :=
  is01_of_toList_eq (s := ("00100" : String)) (cs := ['0', '0', '1', '0', '0']) rfl <| by
    intro c hc
    simpa [or_assoc, or_left_comm, or_comm] using hc

private lemma is01_10010 : Is01String ("10010" : String) :=
  is01_of_toList_eq (s := ("10010" : String)) (cs := ['1', '0', '0', '1', '0']) rfl <| by
    intro c hc
    simpa [or_assoc, or_left_comm, or_comm] using hc

private lemma is01_10100 : Is01String ("10100" : String) :=
  is01_of_toList_eq (s := ("10100" : String)) (cs := ['1', '0', '1', '0', '0']) rfl <| by
    intro c hc
    simpa [or_assoc, or_left_comm, or_comm] using hc

private lemma is01_wA : Is01String wA := by
  rw [wA_eq_pre5]
  exact is01_append (is01_append is01_00100 is01_10010) is01_suf15

private lemma is01_wC : Is01String wC := by
  rw [wC_eq_pre5]
  exact is01_append (is01_append is01_00100 is01_10100) is01_suf15

private lemma row5988_set_eq :
    cylStr (a := (0 : ℤ)) "00100" ∩ cylStr (a := (10 : ℤ)) suf15 =
      cylStr (a := (0 : ℤ)) wA ∪ cylStr (a := (0 : ℤ)) wC := by
  classical
  ext ω
  constructor
  · rintro ⟨hx, hy⟩

    have h0 : ω.1 0 = false := by
      simpa [K5Bridge.wordOfString] using
        (bit_eq_of_mem_cylStr (h := hx) (i := ⟨0, by decide⟩))
    have h1 : ω.1 1 = false := by
      simpa [K5Bridge.wordOfString, add_assoc, add_left_comm, add_comm] using
        (bit_eq_of_mem_cylStr (h := hx) (i := ⟨1, by decide⟩))
    have h2 : ω.1 2 = true := by
      simpa [K5Bridge.wordOfString, add_assoc, add_left_comm, add_comm] using
        (bit_eq_of_mem_cylStr (h := hx) (i := ⟨2, by decide⟩))
    have h3 : ω.1 3 = false := by
      simpa [K5Bridge.wordOfString, add_assoc, add_left_comm, add_comm] using
        (bit_eq_of_mem_cylStr (h := hx) (i := ⟨3, by decide⟩))
    have h4 : ω.1 4 = false := by
      simpa [K5Bridge.wordOfString, add_assoc, add_left_comm, add_comm] using
        (bit_eq_of_mem_cylStr (h := hx) (i := ⟨4, by decide⟩))

    have h5 : ω.1 5 = true := by
      have := twoZeros_next_true ω (i := (3 : ℤ)) (h0 := by simpa [add_assoc] using h3)
        (h1 := by simpa [add_assoc] using h4)
      simpa [add_assoc, add_left_comm, add_comm] using this
    have h6 : ω.1 6 = false := by
      simpa [add_assoc] using true_next_false ω (i := (5 : ℤ)) h5

    have h10 : ω.1 10 = true := by
      simpa [K5Bridge.wordOfString] using
        (bit_eq_of_mem_cylStr (h := hy) (i := ⟨0, by decide⟩))
    have h9 : ω.1 9 = false := by
      simpa [add_assoc, add_left_comm, add_comm, sub_eq_add_neg] using
        true_prev_false ω (i := (10 : ℤ)) h10

    cases h7 : ω.1 7 with
    | false =>
        have h8 : ω.1 8 = true := by
          have := twoZeros_next_true ω (i := (6 : ℤ)) (h0 := by simpa [add_assoc] using h6)
            (h1 := by simpa [add_assoc] using h7)
          simpa [add_assoc, add_left_comm, add_comm] using this
        have hxBS : blockString (a := (0 : ℤ)) 5 ω = ("00100" : String) := by
          have := (mem_cylStr_iff_blockString_eq (a := (0 : ℤ)) ("00100" : String) ω
            is01_00100).1 hx
          simpa using this
        have hyBS : blockString (a := (10 : ℤ)) 15 ω = suf15 := by
          have := (mem_cylStr_iff_blockString_eq (a := (10 : ℤ)) suf15 ω is01_suf15).1 hy
          simpa [suf15_len] using this
        have hgap : ω ∈ cylStr (a := (5 : ℤ)) ("10010" : String) := by
          have hb : FiniteDependence.MIS.Model.block (5 : ℤ) 5 ω =
              K5Bridge.wordOfString ("10010" : String) := by
            funext i
            fin_cases i <;>
              (simp [FiniteDependence.MIS.Model.block, K5Bridge.wordOfString, h5, h6, h7, h8, h9] <;>
                decide)
          simpa [cylStr, FiniteDependence.MIS.Model.cyl] using hb
        have hgapBS : blockString (a := (5 : ℤ)) 5 ω = ("10010" : String) := by
          have := (mem_cylStr_iff_blockString_eq (a := (5 : ℤ)) ("10010" : String) ω
            is01_10010).1 hgap
          simpa using this
        have hfull : blockString (a := (0 : ℤ)) 25 ω = wA := by
          have h1' : blockString (a := (0 : ℤ)) 10 ω = ("00100" : String) ++ ("10010" : String) := by
            calc
              blockString (a := (0 : ℤ)) 10 ω =
                  (blockString (a := (0 : ℤ)) 5 ω) ++ blockString (a := (5 : ℤ)) 5 ω := by
                    simpa using (blockString_add (ω := ω) (a := (0 : ℤ)) (m := 5) (n := 5))
              _ = ("00100" : String) ++ ("10010" : String) := by simpa [hxBS, hgapBS]
          calc
            blockString (a := (0 : ℤ)) 25 ω =
                (blockString (a := (0 : ℤ)) 10 ω) ++ blockString (a := (10 : ℤ)) 15 ω := by
                  simpa using (blockString_add (ω := ω) (a := (0 : ℤ)) (m := 10) (n := 15))
            _ = (("00100" : String) ++ ("10010" : String)) ++ suf15 := by simpa [h1', hyBS]
            _ = wA := by simpa [String.append_assoc, wA_eq_pre5]
        have hwA : ω ∈ cylStr (a := (0 : ℤ)) wA := by
          refine (mem_cylStr_iff_blockString_eq (a := (0 : ℤ)) wA ω is01_wA).2 ?_
          simpa [wA_len] using hfull
        exact Or.inl hwA
    | true =>
        have h8 : ω.1 8 = false := by
          simpa [add_assoc] using true_next_false ω (i := (7 : ℤ)) (by simpa using h7)
        have hxBS : blockString (a := (0 : ℤ)) 5 ω = ("00100" : String) := by
          have := (mem_cylStr_iff_blockString_eq (a := (0 : ℤ)) ("00100" : String) ω
            is01_00100).1 hx
          simpa using this
        have hyBS : blockString (a := (10 : ℤ)) 15 ω = suf15 := by
          have := (mem_cylStr_iff_blockString_eq (a := (10 : ℤ)) suf15 ω is01_suf15).1 hy
          simpa [suf15_len] using this
        have hgap : ω ∈ cylStr (a := (5 : ℤ)) ("10100" : String) := by
          have hb : FiniteDependence.MIS.Model.block (5 : ℤ) 5 ω =
              K5Bridge.wordOfString ("10100" : String) := by
            funext i
            fin_cases i <;>
              (simp [FiniteDependence.MIS.Model.block, K5Bridge.wordOfString, h5, h6, h7, h8, h9] <;>
                decide)
          simpa [cylStr, FiniteDependence.MIS.Model.cyl] using hb
        have hgapBS : blockString (a := (5 : ℤ)) 5 ω = ("10100" : String) := by
          have := (mem_cylStr_iff_blockString_eq (a := (5 : ℤ)) ("10100" : String) ω
            is01_10100).1 hgap
          simpa using this
        have hfull : blockString (a := (0 : ℤ)) 25 ω = wC := by
          have h1' : blockString (a := (0 : ℤ)) 10 ω = ("00100" : String) ++ ("10100" : String) := by
            calc
              blockString (a := (0 : ℤ)) 10 ω =
                  (blockString (a := (0 : ℤ)) 5 ω) ++ blockString (a := (5 : ℤ)) 5 ω := by
                    simpa using (blockString_add (ω := ω) (a := (0 : ℤ)) (m := 5) (n := 5))
              _ = ("00100" : String) ++ ("10100" : String) := by simpa [hxBS, hgapBS]
          calc
            blockString (a := (0 : ℤ)) 25 ω =
                (blockString (a := (0 : ℤ)) 10 ω) ++ blockString (a := (10 : ℤ)) 15 ω := by
                  simpa using (blockString_add (ω := ω) (a := (0 : ℤ)) (m := 10) (n := 15))
            _ = (("00100" : String) ++ ("10100" : String)) ++ suf15 := by simpa [h1', hyBS]
            _ = wC := by simpa [String.append_assoc, wC_eq_pre5]
        have hwC : ω ∈ cylStr (a := (0 : ℤ)) wC := by
          refine (mem_cylStr_iff_blockString_eq (a := (0 : ℤ)) wC ω is01_wC).2 ?_
          simpa [wC_len] using hfull
        exact Or.inr hwC
  · intro hω
    rcases hω with hwA | hwC
    · have hx0 : ω ∈ cylStr (a := (0 : ℤ)) "00100" := by
        have hBS : blockString (a := (0 : ℤ)) 25 ω = wA := by
          have := (mem_cylStr_iff_blockString_eq (a := (0 : ℤ)) wA ω is01_wA).1 hwA
          simpa [wA_len] using this
        have hpref :
            blockString (a := (0 : ℤ)) 5 ω = ("00100" : String) := by
          have := prefixOf_blockString (ω := ω) (a := (0 : ℤ)) (L := 25) (m := 5) (by decide)
          have hw : prefixOf wA 5 = ("00100" : String) := by decide
          simpa [hBS, hw] using this.symm
        exact (mem_cylStr_iff_blockString_eq (a := (0 : ℤ)) ("00100" : String) ω is01_00100).2 hpref
      have hy0 : ω ∈ cylStr (a := (10 : ℤ)) suf15 := by
        have hBS : blockString (a := (0 : ℤ)) 25 ω = wA := by
          have := (mem_cylStr_iff_blockString_eq (a := (0 : ℤ)) wA ω is01_wA).1 hwA
          simpa [wA_len] using this
        have hdrop :
            String.ofList ((blockString (a := (0 : ℤ)) 25 ω).toList.drop 10) =
              blockString (a := (10 : ℤ)) 15 ω := by
          simpa using (ofList_drop_blockString_add (ω := ω) (a := (0 : ℤ)) (m := 10) (n := 15))
        have h1 : blockString (a := (10 : ℤ)) 15 ω = String.ofList (wA.toList.drop 10) := by
          simpa [hBS] using hdrop.symm
        have h2 : String.ofList (wA.toList.drop 10) = suf15 := by decide
        have h10 : blockString (a := (10 : ℤ)) 15 ω = suf15 := h1.trans h2
        exact
          (mem_cylStr_iff_blockString_eq (a := (10 : ℤ)) suf15 ω is01_suf15).2
            (by simpa [suf15_len] using h10)
      exact ⟨hx0, hy0⟩
    · have hx0 : ω ∈ cylStr (a := (0 : ℤ)) "00100" := by
        have hBS : blockString (a := (0 : ℤ)) 25 ω = wC := by
          have := (mem_cylStr_iff_blockString_eq (a := (0 : ℤ)) wC ω is01_wC).1 hwC
          simpa [wC_len] using this
        have hpref :
            blockString (a := (0 : ℤ)) 5 ω = ("00100" : String) := by
          have := prefixOf_blockString (ω := ω) (a := (0 : ℤ)) (L := 25) (m := 5) (by decide)
          have hw : prefixOf wC 5 = ("00100" : String) := by decide
          simpa [hBS, hw] using this.symm
        exact (mem_cylStr_iff_blockString_eq (a := (0 : ℤ)) ("00100" : String) ω is01_00100).2 hpref
      have hy0 : ω ∈ cylStr (a := (10 : ℤ)) suf15 := by
        have hBS : blockString (a := (0 : ℤ)) 25 ω = wC := by
          have := (mem_cylStr_iff_blockString_eq (a := (0 : ℤ)) wC ω is01_wC).1 hwC
          simpa [wC_len] using this
        have hdrop :
            String.ofList ((blockString (a := (0 : ℤ)) 25 ω).toList.drop 10) =
              blockString (a := (10 : ℤ)) 15 ω := by
          simpa using (ofList_drop_blockString_add (ω := ω) (a := (0 : ℤ)) (m := 10) (n := 15))
        have h1 : blockString (a := (10 : ℤ)) 15 ω = String.ofList (wC.toList.drop 10) := by
          simpa [hBS] using hdrop.symm
        have h2 : String.ofList (wC.toList.drop 10) = suf15 := by decide
        have h10 : blockString (a := (10 : ℤ)) 15 ω = suf15 := h1.trans h2
        exact
          (mem_cylStr_iff_blockString_eq (a := (10 : ℤ)) suf15 ω is01_suf15).2
            (by simpa [suf15_len] using h10)
      exact ⟨hx0, hy0⟩

theorem prob_row5988 (μ : Measure FiniteDependence.MIS.State) [IsProbabilityMeasure μ]
    (hstat : Stationary μ) (hdep : KDependent 5 μ) :
    FiniteDependence.MIS.Model.prob μ (cylStr (a := 0) wA) +
        FiniteDependence.MIS.Model.prob μ (cylStr (a := 0) wC) =
      FiniteDependence.MIS.Model.prob μ (cylStr (a := 0) "00100") *
        FiniteDependence.MIS.Model.prob μ (cylStr (a := 0) suf15) := by
  classical
  have hsep : ∀ i : Fin ("00100" : String).length, ∀ j : Fin suf15.length,
      Int.natAbs (((0 : ℤ) + Int.ofNat i.1) - ((10 : ℤ) + Int.ofNat j.1)) > 5 := by
    intro i j
    have hi : i.1 ≤ 4 := Nat.le_of_lt_succ (by
      have : ("00100" : String).length = 5 := by decide
      simpa [this] using i.2)
    have hle10 : i.1 ≤ 10 := le_trans hi (by decide : 4 ≤ 10)
    have hle : i.1 ≤ 10 + j.1 := le_trans hle10 (Nat.le_add_right 10 j.1)

    have habs :
        Int.natAbs ((i.1 : ℤ) - ((10 + j.1 : Nat) : ℤ)) = (10 + j.1) - i.1 := by
      simpa using (natAbs_sub_eq_sub_of_le (a := i.1) (b := 10 + j.1) hle)
    have habs' :
        Int.natAbs (((0 : ℤ) + Int.ofNat i.1) - ((10 : ℤ) + Int.ofNat j.1)) = (10 + j.1) - i.1 := by
      simpa [Int.ofNat_eq_natCast, add_assoc, add_left_comm, add_comm] using habs

    have hdist : 6 ≤ (10 + j.1) - i.1 := by
      have hsub : 10 - 4 ≤ 10 - i.1 := Nat.sub_le_sub_left hi 10
      have h10 : 10 - 4 = 6 := by decide
      have : 6 ≤ 10 - i.1 := by simpa [h10] using hsub
      exact le_trans this (Nat.sub_le_sub_right (Nat.le_add_right 10 j.1) i.1)
    have hgt : (5 : Nat) < (10 + j.1) - i.1 := lt_of_lt_of_le (by decide : 5 < 6) hdist
    rw [habs']
    exact hgt
  have hind :
      FiniteDependence.MIS.Model.prob μ (cylStr (a := (0 : ℤ)) "00100" ∩ cylStr (a := (10 : ℤ)) suf15) =
        FiniteDependence.MIS.Model.prob μ (cylStr (a := (0 : ℤ)) "00100") *
          FiniteDependence.MIS.Model.prob μ (cylStr (a := (10 : ℤ)) suf15) := by
    simpa [cylStr] using
      (FiniteDependence.MIS.Model.KDependent.prob_inter_cyl_eq_mul (μ := μ) (k := 5)
        (m := ("00100" : String).length) (n := suf15.length) (a := (0 : ℤ)) (b := (10 : ℤ)) hdep
        hsep (K5Bridge.wordOfString "00100") (K5Bridge.wordOfString suf15))
  have hshift :
      FiniteDependence.MIS.Model.prob μ (cylStr (a := (10 : ℤ)) suf15) =
        FiniteDependence.MIS.Model.prob μ (cylStr (a := (0 : ℤ)) suf15) := by
    simpa using
      (Stationary.prob_cylStr_add_nat (μ := μ) hstat (a := (0 : ℤ)) (n := 10) (s := suf15))
  have hdisj : Disjoint (cylStr (a := (0 : ℤ)) wA) (cylStr (a := (0 : ℤ)) wC) := by
    have hne : wA ≠ wC := by decide
    exact
      cylStr_disjoint_of_ne_len (a := (0 : ℤ)) (L := 25) (s := wA) (t := wC)
        is01_wA is01_wC wA_len wC_len hne
  have hmeas : MeasurableSet (cylStr (a := (0 : ℤ)) wC) := by
    simpa using measurableSet_cylStr (a := (0 : ℤ)) (s := wC)
  have hunion :
      FiniteDependence.MIS.Model.prob μ (cylStr (a := (0 : ℤ)) wA ∪ cylStr (a := (0 : ℤ)) wC) =
        FiniteDependence.MIS.Model.prob μ (cylStr (a := (0 : ℤ)) wA) +
          FiniteDependence.MIS.Model.prob μ (cylStr (a := (0 : ℤ)) wC) :=
    (FiniteDependence.MIS.Model.prob_union (μ := μ) hdisj hmeas)
  have hset :
      cylStr (a := (0 : ℤ)) "00100" ∩ cylStr (a := (10 : ℤ)) suf15 =
        cylStr (a := (0 : ℤ)) wA ∪ cylStr (a := (0 : ℤ)) wC := row5988_set_eq
  calc
    FiniteDependence.MIS.Model.prob μ (cylStr (a := (0 : ℤ)) wA) +
        FiniteDependence.MIS.Model.prob μ (cylStr (a := (0 : ℤ)) wC)
        = FiniteDependence.MIS.Model.prob μ (cylStr (a := (0 : ℤ)) wA ∪ cylStr (a := (0 : ℤ)) wC) := by
          simpa [hunion]
    _ = FiniteDependence.MIS.Model.prob μ (cylStr (a := (0 : ℤ)) "00100" ∩ cylStr (a := (10 : ℤ)) suf15) := by
          simpa [hset]
    _ = FiniteDependence.MIS.Model.prob μ (cylStr (a := (0 : ℤ)) "00100") *
          FiniteDependence.MIS.Model.prob μ (cylStr (a := (0 : ℤ)) suf15) := by
        simpa [hind, hshift]

end

end Model

end K5Bridge

end FiniteDependence.MIS
