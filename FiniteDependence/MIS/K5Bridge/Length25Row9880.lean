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

private lemma is01_mid10 : Is01String mid10 :=
  is01_of_toList_eq (s := mid10)
    (cs := ['0', '0', '1', '0', '0', '1', '0', '1', '0', '0'])
    rfl <| by
      intro c hc
      simpa [or_assoc, or_left_comm, or_comm] using hc

private lemma is01_10101 : Is01String ("10101" : String) :=
  is01_of_toList_eq (s := ("10101" : String)) (cs := ['1', '0', '1', '0', '1']) rfl <| by
    intro c hc
    simpa [or_assoc, or_left_comm, or_comm] using hc

private lemma is01_wC : Is01String wC := by
  rw [wC_eq_mid10]
  exact is01_append (is01_append is01_mid10 is01_10101) is01_mid10

private lemma row9880_set_eq :
    cylStr (a := (0 : ℤ)) mid10 ∩ cylStr (a := (15 : ℤ)) mid10 = cylStr (a := (0 : ℤ)) wC := by
  classical
  ext ω
  constructor
  · rintro ⟨hx, hy⟩
    have h8 : ω.1 8 = false := by
      simpa [K5Bridge.wordOfString, add_assoc, add_left_comm, add_comm] using
        (bit_eq_of_mem_cylStr (h := hx) (i := ⟨8, by decide⟩))
    have h9 : ω.1 9 = false := by
      simpa [K5Bridge.wordOfString, add_assoc, add_left_comm, add_comm] using
        (bit_eq_of_mem_cylStr (h := hx) (i := ⟨9, by decide⟩))
    have h10 : ω.1 10 = true := by
      have := twoZeros_next_true ω (i := (8 : ℤ)) (h0 := by simpa [add_assoc] using h8)
        (h1 := by simpa [add_assoc] using h9)
      simpa [add_assoc, add_left_comm, add_comm] using this
    have h11 : ω.1 11 = false := by
      simpa [add_assoc] using true_next_false ω (i := (10 : ℤ)) h10

    have h15 : ω.1 15 = false := by
      simpa [K5Bridge.wordOfString] using
        (bit_eq_of_mem_cylStr (h := hy) (i := ⟨0, by decide⟩))
    have h16 : ω.1 16 = false := by
      simpa [K5Bridge.wordOfString, add_assoc, add_left_comm, add_comm] using
        (bit_eq_of_mem_cylStr (h := hy) (i := ⟨1, by decide⟩))
    have h14 : ω.1 14 = true := by
      have := twoZeros_prev_true ω (i := (14 : ℤ)) (h1 := by simpa [add_assoc] using h15)
        (h2 := by simpa [add_assoc] using h16)
      simpa using this
    have h13 : ω.1 13 = false := by
      simpa [add_assoc] using true_prev_false ω (i := (14 : ℤ)) h14

    have h12 : ω.1 12 = true := by
      cases h12v : ω.1 12 with
      | true =>
          simpa using h12v
      | false =>
          have h13' : ω.1 13 = true := by
            have := twoZeros_next_true ω (i := (11 : ℤ)) (h0 := by simpa [add_assoc] using h11)
              (h1 := by simpa [add_assoc] using h12v)
            simpa [add_assoc, add_left_comm, add_comm] using this
          exact False.elim (by simpa [h13] using h13')

    have hxBS : blockString (a := (0 : ℤ)) 10 ω = mid10 := by
      have := (mem_cylStr_iff_blockString_eq (a := (0 : ℤ)) mid10 ω is01_mid10).1 hx
      simpa [mid10_len] using this
    have hyBS : blockString (a := (15 : ℤ)) 10 ω = mid10 := by
      have := (mem_cylStr_iff_blockString_eq (a := (15 : ℤ)) mid10 ω is01_mid10).1 hy
      simpa [mid10_len] using this
    have hgap : ω ∈ cylStr (a := (10 : ℤ)) ("10101" : String) := by
      have hb : FiniteDependence.MIS.Model.block (10 : ℤ) 5 ω =
          K5Bridge.wordOfString ("10101" : String) := by
        funext i
        fin_cases i <;>
          (simp [FiniteDependence.MIS.Model.block, K5Bridge.wordOfString, h10, h11, h12, h13, h14] <;>
            decide)
      simpa [cylStr, FiniteDependence.MIS.Model.cyl] using hb
    have hgapBS : blockString (a := (10 : ℤ)) 5 ω = ("10101" : String) := by
      have := (mem_cylStr_iff_blockString_eq (a := (10 : ℤ)) ("10101" : String) ω is01_10101).1 hgap
      simpa using this
    have hfull : blockString (a := (0 : ℤ)) 25 ω = wC := by
      have h1' : blockString (a := (0 : ℤ)) 15 ω = mid10 ++ ("10101" : String) := by
        calc
          blockString (a := (0 : ℤ)) 15 ω =
              (blockString (a := (0 : ℤ)) 10 ω) ++ blockString (a := (10 : ℤ)) 5 ω := by
                simpa using (blockString_add (ω := ω) (a := (0 : ℤ)) (m := 10) (n := 5))
          _ = mid10 ++ ("10101" : String) := by simpa [hxBS, hgapBS]
      calc
        blockString (a := (0 : ℤ)) 25 ω =
            (blockString (a := (0 : ℤ)) 15 ω) ++ blockString (a := (15 : ℤ)) 10 ω := by
              simpa using (blockString_add (ω := ω) (a := (0 : ℤ)) (m := 15) (n := 10))
        _ = (mid10 ++ ("10101" : String)) ++ mid10 := by simpa [h1', hyBS]
        _ = wC := by simpa [String.append_assoc, wC_eq_mid10]
    exact
      (mem_cylStr_iff_blockString_eq (a := (0 : ℤ)) wC ω is01_wC).2
        (by simpa [wC_len] using hfull)
  · intro hwC
    have hBS : blockString (a := (0 : ℤ)) 25 ω = wC := by
      have := (mem_cylStr_iff_blockString_eq (a := (0 : ℤ)) wC ω is01_wC).1 hwC
      simpa [wC_len] using this
    have hxBS : blockString (a := (0 : ℤ)) 10 ω = mid10 := by
      have := prefixOf_blockString (ω := ω) (a := (0 : ℤ)) (L := 25) (m := 10) (by decide)
      have hw : prefixOf wC 10 = mid10 := by decide
      simpa [hBS, hw] using this.symm
    have hyBS : blockString (a := (15 : ℤ)) 10 ω = mid10 := by
      have hdrop :
          String.ofList ((blockString (a := (0 : ℤ)) 25 ω).toList.drop 15) =
            blockString (a := (15 : ℤ)) 10 ω := by
        simpa using (ofList_drop_blockString_add (ω := ω) (a := (0 : ℤ)) (m := 15) (n := 10))
      have h1 : blockString (a := (15 : ℤ)) 10 ω = String.ofList (wC.toList.drop 15) := by
        simpa [hBS] using hdrop.symm
      have h2 : String.ofList (wC.toList.drop 15) = mid10 := by decide
      exact h1.trans h2
    have hx : ω ∈ cylStr (a := (0 : ℤ)) mid10 :=
      (mem_cylStr_iff_blockString_eq (a := (0 : ℤ)) mid10 ω is01_mid10).2
        (by simpa [mid10_len] using hxBS)
    have hy : ω ∈ cylStr (a := (15 : ℤ)) mid10 :=
      (mem_cylStr_iff_blockString_eq (a := (15 : ℤ)) mid10 ω is01_mid10).2
        (by simpa [mid10_len] using hyBS)
    exact ⟨hx, hy⟩

theorem prob_row9880 (μ : Measure FiniteDependence.MIS.State) [IsProbabilityMeasure μ]
    (hstat : Stationary μ) (hdep : KDependent 5 μ) :
    FiniteDependence.MIS.Model.prob μ (cylStr (a := 0) wC) =
      (FiniteDependence.MIS.Model.prob μ (cylStr (a := 0) mid10)) ^ 2 := by
  classical
  have hsep : ∀ i : Fin mid10.length, ∀ j : Fin mid10.length,
      Int.natAbs (((0 : ℤ) + Int.ofNat i.1) - ((15 : ℤ) + Int.ofNat j.1)) > 5 := by
    intro i j
    have hi : i.1 ≤ 9 := Nat.le_of_lt_succ (by
      have : mid10.length = 10 := by decide
      simpa [this] using i.2)
    have hle15 : i.1 ≤ 15 := le_trans hi (by decide : 9 ≤ 15)
    have hle : i.1 ≤ 15 + j.1 := le_trans hle15 (Nat.le_add_right 15 j.1)

    have habs :
        Int.natAbs ((i.1 : ℤ) - ((15 + j.1 : Nat) : ℤ)) = (15 + j.1) - i.1 := by
      simpa using (natAbs_sub_eq_sub_of_le (a := i.1) (b := 15 + j.1) hle)
    have habs' :
        Int.natAbs (((0 : ℤ) + Int.ofNat i.1) - ((15 : ℤ) + Int.ofNat j.1)) = (15 + j.1) - i.1 := by
      simpa [Int.ofNat_eq_natCast, add_assoc, add_left_comm, add_comm] using habs

    have hdist : 6 ≤ (15 + j.1) - i.1 := by
      have hsub : 15 - 9 ≤ 15 - i.1 := Nat.sub_le_sub_left hi 15
      have h15 : 15 - 9 = 6 := by decide
      have : 6 ≤ 15 - i.1 := by simpa [h15] using hsub
      exact le_trans this (Nat.sub_le_sub_right (Nat.le_add_right 15 j.1) i.1)
    have hgt : (5 : Nat) < (15 + j.1) - i.1 := lt_of_lt_of_le (by decide : 5 < 6) hdist
    rw [habs']
    exact hgt
  have hind :
      FiniteDependence.MIS.Model.prob μ (cylStr (a := (0 : ℤ)) mid10 ∩ cylStr (a := (15 : ℤ)) mid10) =
        FiniteDependence.MIS.Model.prob μ (cylStr (a := (0 : ℤ)) mid10) *
          FiniteDependence.MIS.Model.prob μ (cylStr (a := (15 : ℤ)) mid10) := by
    simpa [cylStr] using
      (FiniteDependence.MIS.Model.KDependent.prob_inter_cyl_eq_mul (μ := μ) (k := 5)
        (m := mid10.length) (n := mid10.length) (a := (0 : ℤ)) (b := (15 : ℤ)) hdep hsep
        (K5Bridge.wordOfString mid10) (K5Bridge.wordOfString mid10))
  have hshift :
      FiniteDependence.MIS.Model.prob μ (cylStr (a := (15 : ℤ)) mid10) =
        FiniteDependence.MIS.Model.prob μ (cylStr (a := (0 : ℤ)) mid10) := by
    simpa using
      (Stationary.prob_cylStr_add_nat (μ := μ) hstat (a := (0 : ℤ)) (n := 15) (s := mid10))
  have hset :
      cylStr (a := (0 : ℤ)) mid10 ∩ cylStr (a := (15 : ℤ)) mid10 = cylStr (a := (0 : ℤ)) wC :=
    row9880_set_eq
  calc
    FiniteDependence.MIS.Model.prob μ (cylStr (a := (0 : ℤ)) wC) =
        FiniteDependence.MIS.Model.prob μ (cylStr (a := (0 : ℤ)) mid10 ∩ cylStr (a := (15 : ℤ)) mid10) := by
          simpa [hset]
    _ = FiniteDependence.MIS.Model.prob μ (cylStr (a := (0 : ℤ)) mid10) *
          FiniteDependence.MIS.Model.prob μ (cylStr (a := (0 : ℤ)) mid10) := by
          simpa [hind, hshift]
    _ = (FiniteDependence.MIS.Model.prob μ (cylStr (a := (0 : ℤ)) mid10)) ^ 2 := by
          simp [pow_two, mul_comm]

end

end Model

end K5Bridge

end FiniteDependence.MIS
