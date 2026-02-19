import FiniteDependence.MIS.K5Bridge.StepLemmas

namespace FiniteDependence.MIS

/-!
## k=5: length-25 “4-row” cancellation

This file proves four *concrete* length-25 identities that hold for any stationary
5-dependent State measure. The key input is that, for these specific prefix/suffix
constraints, the State local rules force at most two completions at length 25.

This avoids enumerating all allowed length-25 words inside Lean.
-/

namespace K5Bridge

open MeasureTheory Set
open scoped ProbabilityTheory

namespace Model

open FiniteDependence.MIS.Model
open K5Data

noncomputable section

/-! ### Local helper lemmas -/

private theorem true_prev_false (ω : FiniteDependence.MIS.State) {i : ℤ} (hi : ω.1 i = true) :
    ω.1 (i - 1) = false := by
  rcases ω.2 with ⟨h11, -⟩
  have hnot : ¬(ω.1 (i - 1) = true ∧ ω.1 ((i - 1) + 1) = true) := h11 (i - 1)
  have : ω.1 (i - 1) ≠ true := by
    intro hprev
    apply hnot
    refine ⟨hprev, ?_⟩
    simpa [sub_eq_add_neg, add_assoc, add_left_comm, add_comm] using hi
  cases h : ω.1 (i - 1)
  · rfl
  · exfalso
    apply this
    simpa using h

private lemma natAbs_sub_eq_sub_of_le {a b : Nat} (hle : a ≤ b) :
    Int.natAbs ((a : ℤ) - (b : ℤ)) = b - a := by
  have hsub : (Int.ofNat (b - a) : ℤ) = (b : ℤ) - (a : ℤ) := by
    exact (Int.ofNat_sub (m := a) (n := b) hle)
  have hneg : ((a : ℤ) - (b : ℤ)) = -((b : ℤ) - (a : ℤ)) := by
    simp [sub_eq_add_neg, add_comm]
  have h1 : Int.natAbs ((a : ℤ) - (b : ℤ)) = Int.natAbs (-((b : ℤ) - (a : ℤ))) := by
    simpa using congrArg Int.natAbs hneg
  have h2 : Int.natAbs (-((b : ℤ) - (a : ℤ))) = Int.natAbs ((b : ℤ) - (a : ℤ)) := by
    simpa using (Int.natAbs_neg ((b : ℤ) - (a : ℤ)))
  calc
    Int.natAbs ((a : ℤ) - (b : ℤ)) = Int.natAbs ((b : ℤ) - (a : ℤ)) := by
      simpa [h1] using h2
    _ = b - a := by
      rw [← hsub]
      rfl

private lemma bit_eq_of_mem_cylStr {a : ℤ} {s : String} {ω : FiniteDependence.MIS.State}
    (h : ω ∈ cylStr (a := a) s) (i : Fin s.length) :
    ω.1 (a + Int.ofNat i.1) = K5Bridge.wordOfString s i := by
  have hcyl : ω ∈ FiniteDependence.MIS.Model.cyl a (K5Bridge.wordOfString s) := by
    simpa [cylStr] using h
  simpa using (FiniteDependence.MIS.Model.bit_eq_of_mem_cyl (h := hcyl) (i := i))

/-! ### Words -/

def wA : String := "0010010010101010010010100"
def wB : String := "0101010010101010010010100"
def wC : String := "0010010100101010010010100"

def suf19 : String := "0010101010010010100"
def suf15 : String := "101010010010100"
def mid10 : String := "0010010100"
def suf24 : String := "101010010101010010010100"

/-! ### Small string facts -/

private lemma wA_len : wA.length = 25 := by native_decide
private lemma wB_len : wB.length = 25 := by native_decide
private lemma wC_len : wC.length = 25 := by native_decide

private lemma suf19_len : suf19.length = 19 := by native_decide
private lemma suf15_len : suf15.length = 15 := by native_decide
private lemma mid10_len : mid10.length = 10 := by native_decide
private lemma suf24_len : suf24.length = 24 := by native_decide

/-! ### Binary-string facts (`Is01String`) -/

private lemma wA_mem_allowedWords25 : wA ∈ K5Data.allowedWords 25 := by native_decide
private lemma wB_mem_allowedWords25 : wB ∈ K5Data.allowedWords 25 := by native_decide
private lemma wC_mem_allowedWords25 : wC ∈ K5Data.allowedWords 25 := by native_decide
private lemma suf19_mem_allowedWords19 : suf19 ∈ K5Data.allowedWords 19 := by native_decide
private lemma suf15_mem_allowedWords15 : suf15 ∈ K5Data.allowedWords 15 := by native_decide
private lemma mid10_mem_allowedWords10 : mid10 ∈ K5Data.allowedWords 10 := by native_decide
private lemma suf24_mem_allowedWords24 : suf24 ∈ K5Data.allowedWords 24 := by native_decide

private lemma str0_mem_allowedWords1 : ("0" : String) ∈ K5Data.allowedWords 1 := by native_decide
private lemma str00100_mem_allowedWords5 : ("00100" : String) ∈ K5Data.allowedWords 5 := by native_decide
private lemma str001001_mem_allowedWords6 : ("001001" : String) ∈ K5Data.allowedWords 6 := by native_decide
private lemma str010101_mem_allowedWords6 : ("010101" : String) ∈ K5Data.allowedWords 6 := by native_decide
private lemma str10010_mem_allowedWords5 : ("10010" : String) ∈ K5Data.allowedWords 5 := by native_decide
private lemma str10100_mem_allowedWords5 : ("10100" : String) ∈ K5Data.allowedWords 5 := by native_decide
private lemma str10101_mem_allowedWords5 : ("10101" : String) ∈ K5Data.allowedWords 5 := by native_decide

private lemma is01_wA : Is01String wA :=
  Is01String.of_mem_allowedWords (L := 25) (s := wA) wA_mem_allowedWords25
private lemma is01_wB : Is01String wB :=
  Is01String.of_mem_allowedWords (L := 25) (s := wB) wB_mem_allowedWords25
private lemma is01_wC : Is01String wC :=
  Is01String.of_mem_allowedWords (L := 25) (s := wC) wC_mem_allowedWords25
private lemma is01_suf19 : Is01String suf19 :=
  Is01String.of_mem_allowedWords (L := 19) (s := suf19) suf19_mem_allowedWords19
private lemma is01_suf15 : Is01String suf15 :=
  Is01String.of_mem_allowedWords (L := 15) (s := suf15) suf15_mem_allowedWords15
private lemma is01_mid10 : Is01String mid10 :=
  Is01String.of_mem_allowedWords (L := 10) (s := mid10) mid10_mem_allowedWords10
private lemma is01_suf24 : Is01String suf24 :=
  Is01String.of_mem_allowedWords (L := 24) (s := suf24) suf24_mem_allowedWords24
private lemma is01_0 : Is01String ("0" : String) :=
  Is01String.of_mem_allowedWords (L := 1) (s := ("0" : String)) str0_mem_allowedWords1
private lemma is01_00100 : Is01String ("00100" : String) :=
  Is01String.of_mem_allowedWords (L := 5) (s := ("00100" : String)) str00100_mem_allowedWords5
private lemma is01_001001 : Is01String ("001001" : String) :=
  Is01String.of_mem_allowedWords (L := 6) (s := ("001001" : String)) str001001_mem_allowedWords6
private lemma is01_010101 : Is01String ("010101" : String) :=
  Is01String.of_mem_allowedWords (L := 6) (s := ("010101" : String)) str010101_mem_allowedWords6

private lemma wA_eq_pre6 : wA = ("001001" : String) ++ suf19 := by native_decide
private lemma wB_eq_pre6 : wB = ("010101" : String) ++ suf19 := by native_decide

private lemma wA_eq_pre5 : wA = ("00100" : String) ++ ("10010" : String) ++ suf15 := by native_decide
private lemma wC_eq_pre5 : wC = ("00100" : String) ++ ("10100" : String) ++ suf15 := by native_decide

private lemma wC_eq_mid10 : wC = mid10 ++ ("10101" : String) ++ mid10 := by native_decide
private lemma wB_eq_suf24 : wB = ("0" : String) ++ suf24 := by native_decide

private lemma is01_10010 : Is01String ("10010" : String) :=
  Is01String.of_mem_allowedWords (L := 5) (s := ("10010" : String)) str10010_mem_allowedWords5
private lemma is01_10100 : Is01String ("10100" : String) :=
  Is01String.of_mem_allowedWords (L := 5) (s := ("10100" : String)) str10100_mem_allowedWords5
private lemma is01_10101 : Is01String ("10101" : String) :=
  Is01String.of_mem_allowedWords (L := 5) (s := ("10101" : String)) str10101_mem_allowedWords5

/-!
`blockString` concatenation: the `m+n`-block is the `m`-block followed by the `n`-block.
-/
private lemma blockString_add (ω : FiniteDependence.MIS.State) (a : ℤ) (m n : Nat) :
    blockString a (m + n) ω = (blockString a m ω) ++ (blockString (a + m) n ω) := by
  apply String.ext
  -- Compare `toList`s.
  simpa [String.toList_append] using
    (toList_blockString_add (ω := ω) (a := a) (m := m) (n := n))

/-! ### Row 2936: prefix 0 at 0, suffix `suf19` at 6 -/

private lemma row2936_set_eq :
    cylStr (a := (0 : ℤ)) "0" ∩ cylStr (a := (6 : ℤ)) suf19 =
      cylStr (a := (0 : ℤ)) wA ∪ cylStr (a := (0 : ℤ)) wB := by
  classical
  ext ω
  constructor
  · rintro ⟨hx, hy⟩

    -- Extract the two suffix bits `X_6 = X_7 = 0`.
    have h6 : ω.1 6 = false := by
      simpa [K5Bridge.wordOfString] using
        (bit_eq_of_mem_cylStr (h := hy) (i := ⟨0, by native_decide⟩))
    have h7 : ω.1 7 = false := by
      simpa [K5Bridge.wordOfString, add_assoc, add_left_comm, add_comm] using
        (bit_eq_of_mem_cylStr (h := hy) (i := ⟨1, by native_decide⟩))

    -- Forced neighbors from State rules.
    have h5 : ω.1 5 = true := by
      -- `X_6 = X_7 = 0` forbids `000` at (5,6,7).
      have := twoZeros_prev_true ω (i := (5 : ℤ)) (h1 := by simpa [add_assoc] using h6)
        (h2 := by simpa [add_assoc] using h7)
      simpa using this
    have h4 : ω.1 4 = false := by
      -- No adjacent `11`.
      simpa [add_assoc] using true_prev_false ω (i := (5 : ℤ)) h5

    -- Also `X_0 = 0`.
    have h0 : ω.1 0 = false := by
      simpa [K5Bridge.wordOfString] using
        (bit_eq_of_mem_cylStr (h := hx) (i := ⟨0, by native_decide⟩))

    -- Split on `X_1`.
    cases h1 : ω.1 1 with
    | false =>
        -- Then `X_2 = 1` (else `000` at 0,1,2), and so `X_3 = 0`.
        have h2 : ω.1 2 = true := by
          have := twoZeros_next_true ω (i := (0 : ℤ)) (h0 := by simpa using h0)
            (h1 := by simpa [h1] using rfl)
          simpa [add_assoc] using this
        have h3 : ω.1 3 = false := by
          simpa [add_assoc] using true_next_false ω (i := (2 : ℤ)) h2

        -- `blockString 0 6 = "001001"`.
        have hpre : ω ∈ cylStr (a := (0 : ℤ)) ("001001" : String) := by
          have hb : FiniteDependence.MIS.Model.block (0 : ℤ) 6 ω = K5Bridge.wordOfString ("001001" : String) := by
            funext i
            fin_cases i <;>
              (simp [FiniteDependence.MIS.Model.block, K5Bridge.wordOfString, h0, h1, h2, h3, h4, h5] <;> native_decide)
          simpa [cylStr, FiniteDependence.MIS.Model.cyl] using hb

        -- Turn `hpre` and `hy` into a length-25 cylinder.
        have hpreBS : blockString (a := (0 : ℤ)) 6 ω = ("001001" : String) := by
          have := (mem_cylStr_iff_blockString_eq (a := (0 : ℤ)) ("001001" : String) ω is01_001001).1 hpre
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
        -- Then `X_2 = 0` (no adjacent `11`), and to avoid `000` at (2,3,4) we must have `X_3 = 1`.
        have h2 : ω.1 2 = false := by
          simpa [add_assoc] using true_next_false ω (i := (1 : ℤ)) (by simpa using h1)
        have h3 : ω.1 3 = true := by
          -- If `X_3 = 0`, then `X_2 = X_3 = 0` forces `X_4 = 1`, contradicting `h4`.
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

        -- `blockString 0 6 = "010101"`.
        have hpre : ω ∈ cylStr (a := (0 : ℤ)) ("010101" : String) := by
          have hb : FiniteDependence.MIS.Model.block (0 : ℤ) 6 ω = K5Bridge.wordOfString ("010101" : String) := by
            funext i
            fin_cases i <;>
              (simp [FiniteDependence.MIS.Model.block, K5Bridge.wordOfString, h0, h1, h2, h3, h4, h5] <;> native_decide)
          simpa [cylStr, FiniteDependence.MIS.Model.cyl] using hb

        have hpreBS : blockString (a := (0 : ℤ)) 6 ω = ("010101" : String) := by
          have := (mem_cylStr_iff_blockString_eq (a := (0 : ℤ)) ("010101" : String) ω is01_010101).1 hpre
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
    · -- `wA` implies both constraints.
      have hBS : blockString (a := (0 : ℤ)) 25 ω = wA := by
        have := (mem_cylStr_iff_blockString_eq (a := (0 : ℤ)) wA ω is01_wA).1 hwA
        simpa [wA_len] using this
      have h0BS : blockString (a := (0 : ℤ)) 1 ω = ("0" : String) := by
        have hpref : prefixOf (blockString (a := (0 : ℤ)) 25 ω) 1 = blockString (a := (0 : ℤ)) 1 ω :=
          prefixOf_blockString (ω := ω) (a := (0 : ℤ)) (L := 25) (m := 1) (by decide)
        have : blockString (a := (0 : ℤ)) 1 ω = prefixOf wA 1 := by
          simpa [hBS] using hpref.symm
        have : blockString (a := (0 : ℤ)) 1 ω = ("0" : String) := by
          simpa [this] using (by native_decide : prefixOf wA 1 = ("0" : String))
        simpa using this
      have hx : ω ∈ cylStr (a := (0 : ℤ)) "0" :=
        (mem_cylStr_iff_blockString_eq (a := (0 : ℤ)) ("0" : String) ω is01_0).2 (by simpa using h0BS)
      have hyBS : blockString (a := (6 : ℤ)) 19 ω = suf19 := by
        have hdrop :
            String.ofList ((blockString (a := (0 : ℤ)) 25 ω).toList.drop 6) =
              blockString (a := (0 : ℤ) + 6) 19 ω := by
          simpa using (ofList_drop_blockString_add (ω := ω) (a := (0 : ℤ)) (m := 6) (n := 19))
        have hBS' : blockString (a := (6 : ℤ)) 19 ω = String.ofList (wA.toList.drop 6) := by
          simpa [hBS] using hdrop.symm
        -- `wA` was chosen so that dropping the first 6 bits yields `suf19`.
        have hwA_drop : String.ofList (wA.toList.drop 6) = suf19 := by native_decide
        simpa [hwA_drop] using hBS'
      have hy : ω ∈ cylStr (a := (6 : ℤ)) suf19 :=
        (mem_cylStr_iff_blockString_eq (a := (6 : ℤ)) suf19 ω is01_suf19).2 (by simpa [suf19_len] using hyBS)
      exact ⟨hx, hy⟩
    · -- `wB` implies both constraints.
      have hBS : blockString (a := (0 : ℤ)) 25 ω = wB := by
        have := (mem_cylStr_iff_blockString_eq (a := (0 : ℤ)) wB ω is01_wB).1 hwB
        simpa [wB_len] using this
      have h0BS : blockString (a := (0 : ℤ)) 1 ω = ("0" : String) := by
        have hpref : prefixOf (blockString (a := (0 : ℤ)) 25 ω) 1 = blockString (a := (0 : ℤ)) 1 ω :=
          prefixOf_blockString (ω := ω) (a := (0 : ℤ)) (L := 25) (m := 1) (by decide)
        have : blockString (a := (0 : ℤ)) 1 ω = prefixOf wB 1 := by
          simpa [hBS] using hpref.symm
        have : blockString (a := (0 : ℤ)) 1 ω = ("0" : String) := by
          simpa [this] using (by native_decide : prefixOf wB 1 = ("0" : String))
        simpa using this
      have hx : ω ∈ cylStr (a := (0 : ℤ)) "0" :=
        (mem_cylStr_iff_blockString_eq (a := (0 : ℤ)) ("0" : String) ω is01_0).2 (by simpa using h0BS)
      have hyBS : blockString (a := (6 : ℤ)) 19 ω = suf19 := by
        have hdrop :
            String.ofList ((blockString (a := (0 : ℤ)) 25 ω).toList.drop 6) =
              blockString (a := (0 : ℤ) + 6) 19 ω := by
          simpa using (ofList_drop_blockString_add (ω := ω) (a := (0 : ℤ)) (m := 6) (n := 19))
        have hBS' : blockString (a := (6 : ℤ)) 19 ω = String.ofList (wB.toList.drop 6) := by
          simpa [hBS] using hdrop.symm
        have hwB_drop : String.ofList (wB.toList.drop 6) = suf19 := by native_decide
        simpa [hwB_drop] using hBS'
      have hy : ω ∈ cylStr (a := (6 : ℤ)) suf19 :=
        (mem_cylStr_iff_blockString_eq (a := (6 : ℤ)) suf19 ω is01_suf19).2 (by simpa [suf19_len] using hyBS)
      exact ⟨hx, hy⟩

theorem prob_row2936 (μ : Measure FiniteDependence.MIS.State) [IsProbabilityMeasure μ]
    (hstat : Stationary μ) (hdep : KDependent 5 μ) :
    FiniteDependence.MIS.Model.prob μ (cylStr (a := 0) wA) +
        FiniteDependence.MIS.Model.prob μ (cylStr (a := 0) wB) =
      FiniteDependence.MIS.Model.prob μ (cylStr (a := 0) "0") *
        FiniteDependence.MIS.Model.prob μ (cylStr (a := 0) suf19) := by
  classical
  -- Independence between `{0}` and `{6..24}`.
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
    -- Different length-25 words give disjoint cylinders.
    have hne : wA ≠ wB := by native_decide
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

  -- Use the set equality to rewrite the intersection probability as a sum.
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

/-! ### Row 5988: prefix `00100` at 0, suffix `suf15` at 10 -/

private lemma row5988_set_eq :
    cylStr (a := (0 : ℤ)) "00100" ∩ cylStr (a := (10 : ℤ)) suf15 =
      cylStr (a := (0 : ℤ)) wA ∪ cylStr (a := (0 : ℤ)) wC := by
  classical
  ext ω
  constructor
  · rintro ⟨hx, hy⟩

    -- Extract `X_0..4 = 00100`.
    have h0 : ω.1 0 = false := by
      simpa [K5Bridge.wordOfString] using
        (bit_eq_of_mem_cylStr (h := hx) (i := ⟨0, by native_decide⟩))
    have h1 : ω.1 1 = false := by
      simpa [K5Bridge.wordOfString, add_assoc, add_left_comm, add_comm] using
        (bit_eq_of_mem_cylStr (h := hx) (i := ⟨1, by native_decide⟩))
    have h2 : ω.1 2 = true := by
      simpa [K5Bridge.wordOfString, add_assoc, add_left_comm, add_comm] using
        (bit_eq_of_mem_cylStr (h := hx) (i := ⟨2, by native_decide⟩))
    have h3 : ω.1 3 = false := by
      simpa [K5Bridge.wordOfString, add_assoc, add_left_comm, add_comm] using
        (bit_eq_of_mem_cylStr (h := hx) (i := ⟨3, by native_decide⟩))
    have h4 : ω.1 4 = false := by
      simpa [K5Bridge.wordOfString, add_assoc, add_left_comm, add_comm] using
        (bit_eq_of_mem_cylStr (h := hx) (i := ⟨4, by native_decide⟩))

    -- From `00` at (3,4), maximality forces `X_5 = 1`, then `X_6 = 0`.
    have h5 : ω.1 5 = true := by
      have := twoZeros_next_true ω (i := (3 : ℤ)) (h0 := by simpa [add_assoc] using h3)
        (h1 := by simpa [add_assoc] using h4)
      simpa [add_assoc, add_left_comm, add_comm] using this
    have h6 : ω.1 6 = false := by
      simpa [add_assoc] using true_next_false ω (i := (5 : ℤ)) h5

    -- Extract `X_10 = 1` from the suffix cylinder, hence `X_9 = 0`.
    have h10 : ω.1 10 = true := by
      simpa [K5Bridge.wordOfString] using
        (bit_eq_of_mem_cylStr (h := hy) (i := ⟨0, by native_decide⟩))
    have h9 : ω.1 9 = false := by
      simpa [add_assoc, add_left_comm, add_comm, sub_eq_add_neg] using
        true_prev_false ω (i := (10 : ℤ)) h10

    -- Split on `X_7`: this determines the 5-bit gap at positions 5..9.
    cases h7 : ω.1 7 with
    | false =>
        -- Then `X_8 = 1` (else `000` at 6,7,8), and `X_9 = 0` is consistent.
        have h8 : ω.1 8 = true := by
          have := twoZeros_next_true ω (i := (6 : ℤ)) (h0 := by simpa [add_assoc] using h6)
            (h1 := by simpa [add_assoc] using h7)
          simpa [add_assoc, add_left_comm, add_comm] using this
        -- Build membership in `wA`.
        have hxBS : blockString (a := (0 : ℤ)) 5 ω = ("00100" : String) := by
          have := (mem_cylStr_iff_blockString_eq (a := (0 : ℤ)) ("00100" : String) ω is01_00100).1 hx
          simpa using this
        have hyBS : blockString (a := (10 : ℤ)) 15 ω = suf15 := by
          have := (mem_cylStr_iff_blockString_eq (a := (10 : ℤ)) suf15 ω is01_suf15).1 hy
          simpa [suf15_len] using this
        have hgap : ω ∈ cylStr (a := (5 : ℤ)) ("10010" : String) := by
          have hb : FiniteDependence.MIS.Model.block (5 : ℤ) 5 ω = K5Bridge.wordOfString ("10010" : String) := by
            funext i
            fin_cases i <;>
              (simp [FiniteDependence.MIS.Model.block, K5Bridge.wordOfString, h5, h6, h7, h8, h9] <;> native_decide)
          simpa [cylStr, FiniteDependence.MIS.Model.cyl] using hb
        have hgapBS : blockString (a := (5 : ℤ)) 5 ω = ("10010" : String) := by
          have := (mem_cylStr_iff_blockString_eq (a := (5 : ℤ)) ("10010" : String) ω is01_10010).1 hgap
          simpa using this
        have hfull : blockString (a := (0 : ℤ)) 25 ω = wA := by
          -- concatenate `0..5`, `5..10`, `10..25`
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
            _ = wA := by
                  -- rewrite associativity then use the precomputed decomposition.
                  simpa [String.append_assoc, wA_eq_pre5]
        have hwA : ω ∈ cylStr (a := (0 : ℤ)) wA := by
          refine (mem_cylStr_iff_blockString_eq (a := (0 : ℤ)) wA ω is01_wA).2 ?_
          simpa [wA_len] using hfull
        exact Or.inl hwA
    | true =>
        -- Then `X_8 = 0` (no `11`), and the gap becomes `10100`.
        have h8 : ω.1 8 = false := by
          simpa [add_assoc] using true_next_false ω (i := (7 : ℤ)) (by simpa using h7)
        have hxBS : blockString (a := (0 : ℤ)) 5 ω = ("00100" : String) := by
          have := (mem_cylStr_iff_blockString_eq (a := (0 : ℤ)) ("00100" : String) ω is01_00100).1 hx
          simpa using this
        have hyBS : blockString (a := (10 : ℤ)) 15 ω = suf15 := by
          have := (mem_cylStr_iff_blockString_eq (a := (10 : ℤ)) suf15 ω is01_suf15).1 hy
          simpa [suf15_len] using this
        have hgap : ω ∈ cylStr (a := (5 : ℤ)) ("10100" : String) := by
          have hb : FiniteDependence.MIS.Model.block (5 : ℤ) 5 ω = K5Bridge.wordOfString ("10100" : String) := by
            funext i
            fin_cases i <;>
              (simp [FiniteDependence.MIS.Model.block, K5Bridge.wordOfString, h5, h6, h7, h8, h9] <;> native_decide)
          simpa [cylStr, FiniteDependence.MIS.Model.cyl] using hb
        have hgapBS : blockString (a := (5 : ℤ)) 5 ω = ("10100" : String) := by
          have := (mem_cylStr_iff_blockString_eq (a := (5 : ℤ)) ("10100" : String) ω is01_10100).1 hgap
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
    · -- `wA` implies both constraints.
      have hx0 : ω ∈ cylStr (a := (0 : ℤ)) "00100" := by
        -- prefix of length 5
        have hBS : blockString (a := (0 : ℤ)) 25 ω = wA := by
          have := (mem_cylStr_iff_blockString_eq (a := (0 : ℤ)) wA ω is01_wA).1 hwA
          simpa [wA_len] using this
        have hpref :
            blockString (a := (0 : ℤ)) 5 ω = ("00100" : String) := by
          have := prefixOf_blockString (ω := ω) (a := (0 : ℤ)) (L := 25) (m := 5) (by decide)
          -- prefixOf wA 5 is 00100
          have hw : prefixOf wA 5 = ("00100" : String) := by native_decide
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
        have h2 : String.ofList (wA.toList.drop 10) = suf15 := by native_decide
        have h10 : blockString (a := (10 : ℤ)) 15 ω = suf15 := h1.trans h2
        exact (mem_cylStr_iff_blockString_eq (a := (10 : ℤ)) suf15 ω is01_suf15).2 (by simpa [suf15_len] using h10)
      exact ⟨hx0, hy0⟩
    · -- `wC` implies both constraints.
      have hx0 : ω ∈ cylStr (a := (0 : ℤ)) "00100" := by
        have hBS : blockString (a := (0 : ℤ)) 25 ω = wC := by
          have := (mem_cylStr_iff_blockString_eq (a := (0 : ℤ)) wC ω is01_wC).1 hwC
          simpa [wC_len] using this
        have hpref :
            blockString (a := (0 : ℤ)) 5 ω = ("00100" : String) := by
          have := prefixOf_blockString (ω := ω) (a := (0 : ℤ)) (L := 25) (m := 5) (by decide)
          have hw : prefixOf wC 5 = ("00100" : String) := by native_decide
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
        have h2 : String.ofList (wC.toList.drop 10) = suf15 := by native_decide
        have h10 : blockString (a := (10 : ℤ)) 15 ω = suf15 := h1.trans h2
        exact (mem_cylStr_iff_blockString_eq (a := (10 : ℤ)) suf15 ω is01_suf15).2 (by simpa [suf15_len] using h10)
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
    -- Since `i ≤ 4`, we have `i ≤ 10 + j`.
    have hi : i.1 ≤ 4 := Nat.le_of_lt_succ (by
      have : ("00100" : String).length = 5 := by native_decide
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
      have h10 : 10 - 4 = 6 := by native_decide
      have : 6 ≤ 10 - i.1 := by simpa [h10] using hsub
      exact le_trans this (Nat.sub_le_sub_right (Nat.le_add_right 10 j.1) i.1)
    have hgt : (5 : Nat) < (10 + j.1) - i.1 := lt_of_lt_of_le (by decide : 5 < 6) hdist
    -- Rewrite the `natAbs` distance and finish.
    rw [habs']
    exact hgt
  have hind :
      FiniteDependence.MIS.Model.prob μ (cylStr (a := (0 : ℤ)) "00100" ∩ cylStr (a := (10 : ℤ)) suf15) =
        FiniteDependence.MIS.Model.prob μ (cylStr (a := (0 : ℤ)) "00100") *
          FiniteDependence.MIS.Model.prob μ (cylStr (a := (10 : ℤ)) suf15) := by
    simpa [cylStr] using
      (FiniteDependence.MIS.Model.KDependent.prob_inter_cyl_eq_mul (μ := μ) (k := 5)
        (m := ("00100" : String).length) (n := suf15.length) (a := (0 : ℤ)) (b := (10 : ℤ)) hdep hsep
        (K5Bridge.wordOfString "00100") (K5Bridge.wordOfString suf15))
  have hshift :
      FiniteDependence.MIS.Model.prob μ (cylStr (a := (10 : ℤ)) suf15) =
        FiniteDependence.MIS.Model.prob μ (cylStr (a := (0 : ℤ)) suf15) := by
    simpa using
      (Stationary.prob_cylStr_add_nat (μ := μ) hstat (a := (0 : ℤ)) (n := 10) (s := suf15))
  have hdisj : Disjoint (cylStr (a := (0 : ℤ)) wA) (cylStr (a := (0 : ℤ)) wC) := by
    have hne : wA ≠ wC := by native_decide
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

/-! ### Row 9880: `mid10` at 0 and 15 forces `wC` -/

private lemma row9880_set_eq :
    cylStr (a := (0 : ℤ)) mid10 ∩ cylStr (a := (15 : ℤ)) mid10 = cylStr (a := (0 : ℤ)) wC := by
  classical
  ext ω
  constructor
  · rintro ⟨hx, hy⟩
    -- Extract the needed boundary bits from the two cylinders.
    have h8 : ω.1 8 = false := by
      simpa [K5Bridge.wordOfString, add_assoc, add_left_comm, add_comm] using
        (bit_eq_of_mem_cylStr (h := hx) (i := ⟨8, by native_decide⟩))
    have h9 : ω.1 9 = false := by
      simpa [K5Bridge.wordOfString, add_assoc, add_left_comm, add_comm] using
        (bit_eq_of_mem_cylStr (h := hx) (i := ⟨9, by native_decide⟩))
    have h10 : ω.1 10 = true := by
      have := twoZeros_next_true ω (i := (8 : ℤ)) (h0 := by simpa [add_assoc] using h8)
        (h1 := by simpa [add_assoc] using h9)
      simpa [add_assoc, add_left_comm, add_comm] using this
    have h11 : ω.1 11 = false := by
      simpa [add_assoc] using true_next_false ω (i := (10 : ℤ)) h10

    have h15 : ω.1 15 = false := by
      simpa [K5Bridge.wordOfString] using
        (bit_eq_of_mem_cylStr (h := hy) (i := ⟨0, by native_decide⟩))
    have h16 : ω.1 16 = false := by
      simpa [K5Bridge.wordOfString, add_assoc, add_left_comm, add_comm] using
        (bit_eq_of_mem_cylStr (h := hy) (i := ⟨1, by native_decide⟩))
    have h14 : ω.1 14 = true := by
      have := twoZeros_prev_true ω (i := (14 : ℤ)) (h1 := by simpa [add_assoc] using h15)
        (h2 := by simpa [add_assoc] using h16)
      simpa using this
    have h13 : ω.1 13 = false := by
      simpa [add_assoc] using true_prev_false ω (i := (14 : ℤ)) h14

    -- Now `X_11 = X_13 = 0` forces `X_12 = 1` to avoid `000`.
    have h12 : ω.1 12 = true := by
      cases h12v : ω.1 12 with
      | true =>
          simpa using h12v
      | false =>
          -- Then `00` at (11,12) forces `X_13 = 1`, contradicting `X_13 = 0`.
          have h13' : ω.1 13 = true := by
            have := twoZeros_next_true ω (i := (11 : ℤ)) (h0 := by simpa [add_assoc] using h11)
              (h1 := by simpa [add_assoc] using h12v)
            simpa [add_assoc, add_left_comm, add_comm] using this
          exact False.elim (by simpa [h13] using h13')

    -- Conclude `blockString 0 25 = wC` by concatenation.
    have hxBS : blockString (a := (0 : ℤ)) 10 ω = mid10 := by
      have := (mem_cylStr_iff_blockString_eq (a := (0 : ℤ)) mid10 ω is01_mid10).1 hx
      simpa [mid10_len] using this
    have hyBS : blockString (a := (15 : ℤ)) 10 ω = mid10 := by
      have := (mem_cylStr_iff_blockString_eq (a := (15 : ℤ)) mid10 ω is01_mid10).1 hy
      simpa [mid10_len] using this
    have hgap : ω ∈ cylStr (a := (10 : ℤ)) ("10101" : String) := by
      have hb : FiniteDependence.MIS.Model.block (10 : ℤ) 5 ω = K5Bridge.wordOfString ("10101" : String) := by
        funext i
        fin_cases i <;>
          (simp [FiniteDependence.MIS.Model.block, K5Bridge.wordOfString, h10, h11, h12, h13, h14] <;> native_decide)
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
    exact (mem_cylStr_iff_blockString_eq (a := (0 : ℤ)) wC ω is01_wC).2 (by simpa [wC_len] using hfull)
  · intro hwC
    -- `wC` clearly implies both `mid10` cylinders.
    have hBS : blockString (a := (0 : ℤ)) 25 ω = wC := by
      have := (mem_cylStr_iff_blockString_eq (a := (0 : ℤ)) wC ω is01_wC).1 hwC
      simpa [wC_len] using this
    have hxBS : blockString (a := (0 : ℤ)) 10 ω = mid10 := by
      have := prefixOf_blockString (ω := ω) (a := (0 : ℤ)) (L := 25) (m := 10) (by decide)
      have hw : prefixOf wC 10 = mid10 := by native_decide
      simpa [hBS, hw] using this.symm
    have hyBS : blockString (a := (15 : ℤ)) 10 ω = mid10 := by
      have hdrop :
          String.ofList ((blockString (a := (0 : ℤ)) 25 ω).toList.drop 15) =
            blockString (a := (15 : ℤ)) 10 ω := by
        simpa using (ofList_drop_blockString_add (ω := ω) (a := (0 : ℤ)) (m := 15) (n := 10))
      have h1 : blockString (a := (15 : ℤ)) 10 ω = String.ofList (wC.toList.drop 15) := by
        simpa [hBS] using hdrop.symm
      have h2 : String.ofList (wC.toList.drop 15) = mid10 := by native_decide
      exact h1.trans h2
    have hx : ω ∈ cylStr (a := (0 : ℤ)) mid10 :=
      (mem_cylStr_iff_blockString_eq (a := (0 : ℤ)) mid10 ω is01_mid10).2 (by simpa [mid10_len] using hxBS)
    have hy : ω ∈ cylStr (a := (15 : ℤ)) mid10 :=
      (mem_cylStr_iff_blockString_eq (a := (15 : ℤ)) mid10 ω is01_mid10).2 (by simpa [mid10_len] using hyBS)
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
      have : mid10.length = 10 := by native_decide
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
      have h15 : 15 - 9 = 6 := by native_decide
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
  -- Now compute.
  calc
    FiniteDependence.MIS.Model.prob μ (cylStr (a := (0 : ℤ)) wC) =
        FiniteDependence.MIS.Model.prob μ (cylStr (a := (0 : ℤ)) mid10 ∩ cylStr (a := (15 : ℤ)) mid10) := by
          simpa [hset]
    _ = FiniteDependence.MIS.Model.prob μ (cylStr (a := (0 : ℤ)) mid10) *
          FiniteDependence.MIS.Model.prob μ (cylStr (a := (0 : ℤ)) mid10) := by
          simpa [hind, hshift]
    _ = (FiniteDependence.MIS.Model.prob μ (cylStr (a := (0 : ℤ)) mid10)) ^ 2 := by
          simp [pow_two, mul_comm]

/-! ### Row 2736: unique extension of `suf24` backwards -/

set_option maxHeartbeats 400000 in
private lemma cylStr_succ_suf24_eq_cylStr_wB :
    cylStr (a := (1 : ℤ)) suf24 = cylStr (a := (0 : ℤ)) wB := by
  classical
  ext ω
  constructor
  · intro h
    -- From `suf24` at position 1, we get `X_1 = 1` and hence `X_0 = 0`, so the 25-block is `0 ++ suf24`.
    have h1 : ω.1 1 = true := by
      simpa [K5Bridge.wordOfString, add_assoc, add_left_comm, add_comm] using
        (bit_eq_of_mem_cylStr (h := h) (i := ⟨0, by native_decide⟩))
    have h0 : ω.1 0 = false := by
      simpa [sub_eq_add_neg, add_assoc, add_left_comm, add_comm] using
        true_prev_false ω (i := (1 : ℤ)) h1
    have h0cyl : ω ∈ cylStr (a := (0 : ℤ)) ("0" : String) := by
      have hb : FiniteDependence.MIS.Model.block (0 : ℤ) ("0" : String).length ω = K5Bridge.wordOfString "0" := by
        funext i
        fin_cases i <;> (simp [FiniteDependence.MIS.Model.block, K5Bridge.wordOfString, h0] <;> native_decide)
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
    -- `wB` at 0 obviously implies `suf24` at 1.
    have hBS : blockString (a := (0 : ℤ)) 25 ω = wB := by
      have := (mem_cylStr_iff_blockString_eq (a := (0 : ℤ)) wB ω is01_wB).1 h
      simpa [wB_len] using this
    have hdrop :
        String.ofList ((blockString (a := (0 : ℤ)) 25 ω).toList.drop 1) =
          blockString (a := (1 : ℤ)) 24 ω := by
      simpa using (ofList_drop_blockString_add (ω := ω) (a := (0 : ℤ)) (m := 1) (n := 24))
    have hBS' : blockString (a := (1 : ℤ)) 24 ω = String.ofList (wB.toList.drop 1) := by
      simpa [hBS] using hdrop.symm
    have hdropEq : String.ofList (wB.toList.drop 1) = suf24 := by native_decide
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
  -- rewrite by the set equality and shift.
  simpa [hset] using hshift

/-! ### Forced cancellation -/

theorem rhs_combination_eq_zero (μ : Measure FiniteDependence.MIS.State) [IsProbabilityMeasure μ]
    (hstat : Stationary μ) (hdep : KDependent 5 μ) :
    (FiniteDependence.MIS.Model.prob μ (cylStr (a := 0) "0") *
          FiniteDependence.MIS.Model.prob μ (cylStr (a := 0) suf19)) +
        (FiniteDependence.MIS.Model.prob μ (cylStr (a := 0) mid10)) ^ 2 -
        FiniteDependence.MIS.Model.prob μ (cylStr (a := 0) suf24) -
        (FiniteDependence.MIS.Model.prob μ (cylStr (a := 0) "00100") *
          FiniteDependence.MIS.Model.prob μ (cylStr (a := 0) suf15)) = 0 := by
  set xA : ℝ := FiniteDependence.MIS.Model.prob μ (cylStr (a := 0) wA)
  set xB : ℝ := FiniteDependence.MIS.Model.prob μ (cylStr (a := 0) wB)
  set xC : ℝ := FiniteDependence.MIS.Model.prob μ (cylStr (a := 0) wC)

  have h2936 :
      xA + xB =
        FiniteDependence.MIS.Model.prob μ (cylStr (a := 0) "0") *
          FiniteDependence.MIS.Model.prob μ (cylStr (a := 0) suf19) := by
    simpa [xA, xB] using prob_row2936 (μ := μ) hstat hdep
  have h9880 :
      xC = (FiniteDependence.MIS.Model.prob μ (cylStr (a := 0) mid10)) ^ 2 := by
    simpa [xC] using prob_row9880 (μ := μ) hstat hdep
  have h2736 :
      xB = FiniteDependence.MIS.Model.prob μ (cylStr (a := 0) suf24) := by
    simpa [xB] using prob_row2736 (μ := μ) hstat
  have h5988 :
      xA + xC =
        FiniteDependence.MIS.Model.prob μ (cylStr (a := 0) "00100") *
          FiniteDependence.MIS.Model.prob μ (cylStr (a := 0) suf15) := by
    simpa [xA, xC] using prob_row5988 (μ := μ) hstat hdep

  have hcancel : (xA + xB) + xC - xB - (xA + xC) = (0 : ℝ) := by ring
  have h1 :
      (FiniteDependence.MIS.Model.prob μ (cylStr (a := 0) "0") *
            FiniteDependence.MIS.Model.prob μ (cylStr (a := 0) suf19)) +
          xC - xB -
            (FiniteDependence.MIS.Model.prob μ (cylStr (a := 0) "00100") *
              FiniteDependence.MIS.Model.prob μ (cylStr (a := 0) suf15)) = (0 : ℝ) := by
    simpa [h2936, h5988] using hcancel
  have h2 :
      (FiniteDependence.MIS.Model.prob μ (cylStr (a := 0) "0") *
            FiniteDependence.MIS.Model.prob μ (cylStr (a := 0) suf19)) +
          (FiniteDependence.MIS.Model.prob μ (cylStr (a := 0) mid10)) ^ 2 -
            FiniteDependence.MIS.Model.prob μ (cylStr (a := 0) suf24) -
            (FiniteDependence.MIS.Model.prob μ (cylStr (a := 0) "00100") *
              FiniteDependence.MIS.Model.prob μ (cylStr (a := 0) suf15)) = (0 : ℝ) := by
    simpa [h9880, h2736, sub_eq_add_neg, add_assoc, add_left_comm, add_comm] using h1
  simpa [sub_eq_add_neg, add_assoc, add_left_comm, add_comm] using h2

end

end Model

end K5Bridge

end FiniteDependence.MIS
