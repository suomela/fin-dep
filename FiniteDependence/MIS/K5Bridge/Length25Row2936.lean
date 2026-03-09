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

private lemma is01_suf19 : Is01String suf19 :=
  is01_of_toList_eq (s := suf19)
    (cs := ['0', '0', '1', '0', '1', '0', '1', '0', '1', '0', '0', '1', '0', '0', '1', '0',
      '1', '0', '0'])
    rfl <| by
      intro c hc
      simpa [or_assoc, or_left_comm, or_comm] using hc

private lemma is01_0 : Is01String ("0" : String) :=
  is01_of_toList_eq (s := ("0" : String)) (cs := ['0']) rfl <| by
    intro c hc
    exact Or.inl (by simpa using hc)

private lemma is01_001001 : Is01String ("001001" : String) :=
  is01_of_toList_eq (s := ("001001" : String)) (cs := ['0', '0', '1', '0', '0', '1']) rfl <| by
    intro c hc
    simpa [or_assoc, or_left_comm, or_comm] using hc

private lemma is01_010101 : Is01String ("010101" : String) :=
  is01_of_toList_eq (s := ("010101" : String)) (cs := ['0', '1', '0', '1', '0', '1']) rfl <| by
    intro c hc
    simpa [or_assoc, or_left_comm, or_comm] using hc

private lemma is01_wA : Is01String wA := by
  rw [wA_eq_pre6]
  exact is01_append is01_001001 is01_suf19

private lemma is01_wB : Is01String wB := by
  rw [wB_eq_pre6]
  exact is01_append is01_010101 is01_suf19

private lemma row2936_set_eq :
    cylStr (a := (0 : ℤ)) "0" ∩ cylStr (a := (6 : ℤ)) suf19 =
      cylStr (a := (0 : ℤ)) wA ∪ cylStr (a := (0 : ℤ)) wB := by
  classical
  ext ω
  constructor
  · rintro ⟨hx, hy⟩

    have h6 : ω.1 6 = false := by
      simpa [K5Bridge.wordOfString] using
        (bit_eq_of_mem_cylStr (h := hy) (i := ⟨0, by decide⟩))
    have h7 : ω.1 7 = false := by
      simpa [K5Bridge.wordOfString, add_assoc, add_left_comm, add_comm] using
        (bit_eq_of_mem_cylStr (h := hy) (i := ⟨1, by decide⟩))

    have h5 : ω.1 5 = true := by
      have := twoZeros_prev_true ω (i := (5 : ℤ)) (h1 := by simpa [add_assoc] using h6)
        (h2 := by simpa [add_assoc] using h7)
      simpa using this
    have h4 : ω.1 4 = false := by
      simpa [add_assoc] using true_prev_false ω (i := (5 : ℤ)) h5

    have h0 : ω.1 0 = false := by
      simpa [K5Bridge.wordOfString] using
        (bit_eq_of_mem_cylStr (h := hx) (i := ⟨0, by decide⟩))

    cases h1 : ω.1 1 with
    | false =>
        have h2 : ω.1 2 = true := by
          have := twoZeros_next_true ω (i := (0 : ℤ)) (h0 := by simpa using h0)
            (h1 := by simpa [h1] using rfl)
          simpa [add_assoc] using this
        have h3 : ω.1 3 = false := by
          simpa [add_assoc] using true_next_false ω (i := (2 : ℤ)) h2

        have hpre : ω ∈ cylStr (a := (0 : ℤ)) ("001001" : String) := by
          have hb : FiniteDependence.MIS.Model.block (0 : ℤ) 6 ω =
              K5Bridge.wordOfString ("001001" : String) := by
            funext i
            fin_cases i <;>
              (simp [FiniteDependence.MIS.Model.block, K5Bridge.wordOfString, h0, h1, h2, h3, h4,
                h5] <;> decide)
          simpa [cylStr, FiniteDependence.MIS.Model.cyl] using hb

        have hpreBS : blockString (a := (0 : ℤ)) 6 ω = ("001001" : String) := by
          have := (mem_cylStr_iff_blockString_eq (a := (0 : ℤ)) ("001001" : String) ω
            is01_001001).1 hpre
          simpa using this
        have hyBS : blockString (a := (6 : ℤ)) 19 ω = suf19 := by
          have := (mem_cylStr_iff_blockString_eq (a := (6 : ℤ)) suf19 ω is01_suf19).1 hy
          simpa [suf19_len] using this
        have hfull : blockString (a := (0 : ℤ)) 25 ω = wA := by
          calc
            blockString (a := (0 : ℤ)) 25 ω =
                (blockString (a := (0 : ℤ)) 6 ω) ++ blockString (a := (6 : ℤ)) 19 ω := by
                  simpa using (blockString_add (ω := ω) (a := (0 : ℤ)) (m := 6) (n := 19))
            _ = ("001001" : String) ++ suf19 := by simpa [hpreBS, hyBS]
            _ = wA := by simpa [wA_eq_pre6] using rfl
        have hwA : ω ∈ cylStr (a := (0 : ℤ)) wA := by
          refine (mem_cylStr_iff_blockString_eq (a := (0 : ℤ)) wA ω is01_wA).2 ?_
          simpa [wA_len] using hfull
        exact Or.inl hwA
    | true =>
        have h2 : ω.1 2 = false := by
          simpa [add_assoc] using true_next_false ω (i := (1 : ℤ)) (by simpa using h1)
        have h3 : ω.1 3 = true := by
          cases h3v : ω.1 3 with
          | true =>
              simpa using h3v
          | false =>
              have h4true : ω.1 4 = true := by
                have := twoZeros_next_true ω (i := (2 : ℤ)) (h0 := by simpa using h2)
                  (h1 := by simpa [add_assoc] using h3v)
                simpa [add_assoc] using this
              have : (false : Bool) = true := by simpa [h4] using h4true
              cases this

        have hpre : ω ∈ cylStr (a := (0 : ℤ)) ("010101" : String) := by
          have hb : FiniteDependence.MIS.Model.block (0 : ℤ) 6 ω =
              K5Bridge.wordOfString ("010101" : String) := by
            funext i
            fin_cases i <;>
              (simp [FiniteDependence.MIS.Model.block, K5Bridge.wordOfString, h0, h1, h2, h3, h4,
                h5] <;> decide)
          simpa [cylStr, FiniteDependence.MIS.Model.cyl] using hb

        have hpreBS : blockString (a := (0 : ℤ)) 6 ω = ("010101" : String) := by
          have := (mem_cylStr_iff_blockString_eq (a := (0 : ℤ)) ("010101" : String) ω
            is01_010101).1 hpre
          simpa using this
        have hyBS : blockString (a := (6 : ℤ)) 19 ω = suf19 := by
          have := (mem_cylStr_iff_blockString_eq (a := (6 : ℤ)) suf19 ω is01_suf19).1 hy
          simpa [suf19_len] using this
        have hfull : blockString (a := (0 : ℤ)) 25 ω = wB := by
          calc
            blockString (a := (0 : ℤ)) 25 ω =
                (blockString (a := (0 : ℤ)) 6 ω) ++ blockString (a := (6 : ℤ)) 19 ω := by
                  simpa using (blockString_add (ω := ω) (a := (0 : ℤ)) (m := 6) (n := 19))
            _ = ("010101" : String) ++ suf19 := by simpa [hpreBS, hyBS]
            _ = wB := by simpa [wB_eq_pre6] using rfl
        have hwB : ω ∈ cylStr (a := (0 : ℤ)) wB := by
          refine (mem_cylStr_iff_blockString_eq (a := (0 : ℤ)) wB ω is01_wB).2 ?_
          simpa [wB_len] using hfull
        exact Or.inr hwB
  · intro hω
    rcases hω with hwA | hwB
    · have hBS : blockString (a := (0 : ℤ)) 25 ω = wA := by
        have := (mem_cylStr_iff_blockString_eq (a := (0 : ℤ)) wA ω is01_wA).1 hwA
        simpa [wA_len] using this
      have h0BS : blockString (a := (0 : ℤ)) 1 ω = ("0" : String) := by
        have hpref : prefixOf (blockString (a := (0 : ℤ)) 25 ω) 1 = blockString (a := (0 : ℤ)) 1 ω :=
          prefixOf_blockString (ω := ω) (a := (0 : ℤ)) (L := 25) (m := 1) (by decide)
        have : blockString (a := (0 : ℤ)) 1 ω = prefixOf wA 1 := by
          simpa [hBS] using hpref.symm
        have : blockString (a := (0 : ℤ)) 1 ω = ("0" : String) := by
          simpa [this] using (by decide : prefixOf wA 1 = ("0" : String))
        simpa using this
      have hx : ω ∈ cylStr (a := (0 : ℤ)) "0" :=
        (mem_cylStr_iff_blockString_eq (a := (0 : ℤ)) ("0" : String) ω is01_0).2
          (by simpa using h0BS)
      have hyBS : blockString (a := (6 : ℤ)) 19 ω = suf19 := by
        have hdrop :
            String.ofList ((blockString (a := (0 : ℤ)) 25 ω).toList.drop 6) =
              blockString (a := (0 : ℤ) + 6) 19 ω := by
          simpa using (ofList_drop_blockString_add (ω := ω) (a := (0 : ℤ)) (m := 6) (n := 19))
        have hBS' : blockString (a := (6 : ℤ)) 19 ω = String.ofList (wA.toList.drop 6) := by
          simpa [hBS] using hdrop.symm
        have hwA_drop : String.ofList (wA.toList.drop 6) = suf19 := by decide
        simpa [hwA_drop] using hBS'
      have hy : ω ∈ cylStr (a := (6 : ℤ)) suf19 :=
        (mem_cylStr_iff_blockString_eq (a := (6 : ℤ)) suf19 ω is01_suf19).2
          (by simpa [suf19_len] using hyBS)
      exact ⟨hx, hy⟩
    · have hBS : blockString (a := (0 : ℤ)) 25 ω = wB := by
        have := (mem_cylStr_iff_blockString_eq (a := (0 : ℤ)) wB ω is01_wB).1 hwB
        simpa [wB_len] using this
      have h0BS : blockString (a := (0 : ℤ)) 1 ω = ("0" : String) := by
        have hpref : prefixOf (blockString (a := (0 : ℤ)) 25 ω) 1 = blockString (a := (0 : ℤ)) 1 ω :=
          prefixOf_blockString (ω := ω) (a := (0 : ℤ)) (L := 25) (m := 1) (by decide)
        have : blockString (a := (0 : ℤ)) 1 ω = prefixOf wB 1 := by
          simpa [hBS] using hpref.symm
        have : blockString (a := (0 : ℤ)) 1 ω = ("0" : String) := by
          simpa [this] using (by decide : prefixOf wB 1 = ("0" : String))
        simpa using this
      have hx : ω ∈ cylStr (a := (0 : ℤ)) "0" :=
        (mem_cylStr_iff_blockString_eq (a := (0 : ℤ)) ("0" : String) ω is01_0).2
          (by simpa using h0BS)
      have hyBS : blockString (a := (6 : ℤ)) 19 ω = suf19 := by
        have hdrop :
            String.ofList ((blockString (a := (0 : ℤ)) 25 ω).toList.drop 6) =
              blockString (a := (0 : ℤ) + 6) 19 ω := by
          simpa using (ofList_drop_blockString_add (ω := ω) (a := (0 : ℤ)) (m := 6) (n := 19))
        have hBS' : blockString (a := (6 : ℤ)) 19 ω = String.ofList (wB.toList.drop 6) := by
          simpa [hBS] using hdrop.symm
        have hwB_drop : String.ofList (wB.toList.drop 6) = suf19 := by decide
        simpa [hwB_drop] using hBS'
      have hy : ω ∈ cylStr (a := (6 : ℤ)) suf19 :=
        (mem_cylStr_iff_blockString_eq (a := (6 : ℤ)) suf19 ω is01_suf19).2
          (by simpa [suf19_len] using hyBS)
      exact ⟨hx, hy⟩

theorem prob_row2936 (μ : Measure FiniteDependence.MIS.State) [IsProbabilityMeasure μ]
    (hstat : Stationary μ) (hdep : KDependent 5 μ) :
    FiniteDependence.MIS.Model.prob μ (cylStr (a := 0) wA) +
        FiniteDependence.MIS.Model.prob μ (cylStr (a := 0) wB) =
      FiniteDependence.MIS.Model.prob μ (cylStr (a := 0) "0") *
        FiniteDependence.MIS.Model.prob μ (cylStr (a := 0) suf19) := by
  classical
  have hsep : ∀ i : Fin ("0" : String).length, ∀ j : Fin suf19.length,
      Int.natAbs (((0 : ℤ) + Int.ofNat i.1) - ((6 : ℤ) + Int.ofNat j.1)) > 5 := by
    intro i j
    fin_cases i
    have hle : (0 : Nat) ≤ 6 + j.1 := Nat.zero_le _
    have habs :
        Int.natAbs ((0 : ℤ) - ((6 + j.1 : Nat) : ℤ)) = 6 + j.1 := by
      simpa using (natAbs_sub_eq_sub_of_le (a := 0) (b := 6 + j.1) hle)
    have habs' :
        Int.natAbs (((0 : ℤ) + Int.ofNat 0) - ((6 : ℤ) + Int.ofNat j.1)) = 6 + j.1 := by
      simpa [Int.ofNat_eq_natCast, add_assoc, add_left_comm, add_comm] using habs
    have hgt : (5 : Nat) < 6 + j.1 := lt_of_lt_of_le (by decide : 5 < 6) (Nat.le_add_right 6 j.1)
    rw [habs']
    exact hgt
  have hind :
      FiniteDependence.MIS.Model.prob μ (cylStr (a := (0 : ℤ)) "0" ∩ cylStr (a := (6 : ℤ)) suf19) =
        FiniteDependence.MIS.Model.prob μ (cylStr (a := (0 : ℤ)) "0") *
          FiniteDependence.MIS.Model.prob μ (cylStr (a := (6 : ℤ)) suf19) := by
    simpa [cylStr] using
      (FiniteDependence.MIS.Model.KDependent.prob_inter_cyl_eq_mul (μ := μ) (k := 5)
        (m := ("0" : String).length) (n := suf19.length) (a := (0 : ℤ)) (b := (6 : ℤ)) hdep hsep
        (K5Bridge.wordOfString "0") (K5Bridge.wordOfString suf19))
  have hshift :
      FiniteDependence.MIS.Model.prob μ (cylStr (a := (6 : ℤ)) suf19) =
        FiniteDependence.MIS.Model.prob μ (cylStr (a := (0 : ℤ)) suf19) := by
    simpa using
      (Stationary.prob_cylStr_add_nat (μ := μ) hstat (a := (0 : ℤ)) (n := 6) (s := suf19))
  have hdisj : Disjoint (cylStr (a := (0 : ℤ)) wA) (cylStr (a := (0 : ℤ)) wB) := by
    have hne : wA ≠ wB := by decide
    exact
      cylStr_disjoint_of_ne_len (a := (0 : ℤ)) (L := 25) (s := wA) (t := wB)
        is01_wA is01_wB wA_len wB_len hne
  have hmeas : MeasurableSet (cylStr (a := (0 : ℤ)) wB) := by
    simpa using measurableSet_cylStr (a := (0 : ℤ)) (s := wB)
  have hunion :
      FiniteDependence.MIS.Model.prob μ (cylStr (a := (0 : ℤ)) wA ∪ cylStr (a := (0 : ℤ)) wB) =
        FiniteDependence.MIS.Model.prob μ (cylStr (a := (0 : ℤ)) wA) +
          FiniteDependence.MIS.Model.prob μ (cylStr (a := (0 : ℤ)) wB) :=
    (FiniteDependence.MIS.Model.prob_union (μ := μ) hdisj hmeas)

  have hset :
      cylStr (a := (0 : ℤ)) "0" ∩ cylStr (a := (6 : ℤ)) suf19 =
        cylStr (a := (0 : ℤ)) wA ∪ cylStr (a := (0 : ℤ)) wB := row2936_set_eq
  calc
    FiniteDependence.MIS.Model.prob μ (cylStr (a := (0 : ℤ)) wA) +
        FiniteDependence.MIS.Model.prob μ (cylStr (a := (0 : ℤ)) wB)
        = FiniteDependence.MIS.Model.prob μ (cylStr (a := (0 : ℤ)) wA ∪ cylStr (a := (0 : ℤ)) wB) := by
          simpa [hunion]
    _ = FiniteDependence.MIS.Model.prob μ (cylStr (a := (0 : ℤ)) "0" ∩ cylStr (a := (6 : ℤ)) suf19) := by
          simpa [hset]
    _ = FiniteDependence.MIS.Model.prob μ (cylStr (a := (0 : ℤ)) "0") *
          FiniteDependence.MIS.Model.prob μ (cylStr (a := (0 : ℤ)) suf19) := by
        simpa [hind, hshift]

end

end Model

end K5Bridge

end FiniteDependence.MIS
