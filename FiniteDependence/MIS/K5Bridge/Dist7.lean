import FiniteDependence.MIS.K5Bridge.PrefixSums
import FiniteDependence.MIS.Prob

namespace FiniteDependence.MIS

/-!
Length-7 word probabilities forced by stationarity + 5-dependence.

This is the analytic starting point of the k=5 certificate: the length-7 cylinder
probabilities are an explicit affine family in

`p := P("1")` and `t := P("1010101")`.

We prove these formulas directly on the abstract MIS model (`Model.lean`), using only:
- stationarity on length 6 (prefix vs one-step suffix sums), and
- independence of coordinates at distance 6 (> 5).
-/

open MeasureTheory Set

open scoped BigOperators ProbabilityTheory

namespace K5Bridge

namespace Model

open FiniteDependence.MIS.Model
open K5Data

noncomputable section

/-! ### Helper finsets on `allowedWords 7` -/

def pref6 (u : String) : Finset String :=
  (allowedWordsFinset 7).filter (fun w => prefixOf w 6 = u)

def suf6 (u : String) : Finset String :=
  (allowedWordsFinset 7).filter (fun w => suffix1 w = u)

def good11 : Finset String :=
  (allowedWordsFinset 7).filter (fun w => prefixOf w 1 = "1" ∧ w.toList.reverse.head? = some '1')

def good00 : Finset String :=
  (allowedWordsFinset 7).filter (fun w => prefixOf w 1 = "0" ∧ w.toList.reverse.head? = some '0')

def good01 : Finset String :=
  (allowedWordsFinset 7).filter (fun w => prefixOf w 1 = "0" ∧ w.toList.reverse.head? = some '1')

lemma pref6_001001 : pref6 "001001" = {"0010010"} := by native_decide
lemma suf6_001001 : suf6 "001001" = {"1001001"} := by native_decide

lemma pref6_100100 : pref6 "100100" = {"1001001"} := by native_decide
lemma suf6_100100 : suf6 "100100" = {"0100100"} := by native_decide

lemma pref6_001010 : pref6 "001010" = {"0010100", "0010101"} := by native_decide
lemma suf6_001010 : suf6 "001010" = {"1001010"} := by native_decide

lemma pref6_100101 : pref6 "100101" = {"1001010"} := by native_decide
lemma suf6_100101 : suf6 "100101" = {"0100101"} := by native_decide

lemma pref6_010010 : pref6 "010010" = {"0100100", "0100101"} := by native_decide
lemma suf6_010010 : suf6 "010010" = {"0010010", "1010010"} := by native_decide

lemma pref6_010100 : pref6 "010100" = {"0101001"} := by native_decide
lemma suf6_010100 : suf6 "010100" = {"0010100", "1010100"} := by native_decide

lemma pref6_101001 : pref6 "101001" = {"1010010"} := by native_decide
lemma suf6_101001 : suf6 "101001" = {"0101001"} := by native_decide

lemma pref6_010101 : pref6 "010101" = {"0101010"} := by native_decide
lemma suf6_010101 : suf6 "010101" = {"0010101", "1010101"} := by native_decide

lemma pref6_101010 : pref6 "101010" = {"1010100", "1010101"} := by native_decide
lemma suf6_101010 : suf6 "101010" = {"0101010"} := by native_decide

lemma good11_eq : good11 = {"1001001", "1010101"} := by native_decide
lemma good00_eq : good00 = {"0010010", "0010100", "0100100", "0101010"} := by native_decide
lemma good01_eq : good01 = {"0010101", "0100101", "0101001"} := by native_decide

/-! ### Basic 1-step stationarity on cylinders -/

theorem prob_cylStr_add_nat {μ : Measure FiniteDependence.MIS.State} [IsProbabilityMeasure μ]
    (hstat : Stationary μ) (a : ℤ) (s : String) :
    ∀ n : Nat, FiniteDependence.MIS.Model.prob μ (cylStr (a := a + n) s) =
      FiniteDependence.MIS.Model.prob μ (cylStr (a := a) s) := by
  intro n
  induction n with
  | zero =>
      simp
  | succ n ih =>
      have hs :
          FiniteDependence.MIS.Model.prob μ (cylStr (a := a + n + 1) s) =
            FiniteDependence.MIS.Model.prob μ (cylStr (a := a + n) s) := by
        simpa [add_assoc] using (Stationary.prob_cylStr_succ (μ := μ) hstat (a := a + n) (s := s))
      simpa [Nat.succ_eq_add_one, add_assoc] using hs.trans ih

theorem prob_cylStr0_0_eq_one_sub_prob1 {μ : Measure FiniteDependence.MIS.State} [IsProbabilityMeasure μ] :
    FiniteDependence.MIS.Model.prob μ (cylStr (a := 0) "0") =
      1 - FiniteDependence.MIS.Model.prob μ (cylStr (a := 0) "1") := by
  classical
  have h01 : ("0" : String) ∈ K5Data.allowedWords 1 := by native_decide
  have h11 : ("1" : String) ∈ K5Data.allowedWords 1 := by native_decide
  have h0meas : MeasurableSet (cylStr (a := 0) ("0" : String)) := measurableSet_cylStr (a := 0) (s := "0")
  have hdisj : Disjoint (cylStr (a := 0) ("0" : String)) (cylStr (a := 0) ("1" : String)) := by
    -- Distinct length-1 cylinders are disjoint.
    have h0 : Is01String ("0" : String) := Is01String.of_mem_allowedWords (L := 1) (s := "0") h01
    have h1 : Is01String ("1" : String) := Is01String.of_mem_allowedWords (L := 1) (s := "1") h11
    have h0L : ("0" : String).length = 1 := length_of_mem_allowedWords (L := 1) (s := "0") h01
    have h1L : ("1" : String).length = 1 := length_of_mem_allowedWords (L := 1) (s := "1") h11
    exact cylStr_disjoint_of_ne_len (a := 0) (L := 1) (s := "0") (t := "1") h0 h1 h0L h1L (by native_decide)
  have hcover : cylStr (a := 0) ("0" : String) ∪ cylStr (a := 0) ("1" : String) = (univ : Set FiniteDependence.MIS.State) := by
    -- Every State configuration has a well-defined bit at 0.
    ext ω
    constructor
    · intro _; exact mem_univ ω
    · intro _
      -- split on the bit at 0
      cases h : ω.1 0 with
      | false =>
          refine Or.inl ?_
          have hb : blockString 0 1 ω = "0" := by
            simp [K5Bridge.Model.blockString, h]
            native_decide
          have h01' : Is01String ("0" : String) := Is01String.of_mem_allowedWords (L := 1) (s := "0") h01
          exact (mem_cylStr_iff_blockString_eq (a := 0) ("0" : String) ω h01').2 (by simpa using hb)
      | true =>
          refine Or.inr ?_
          have hb : blockString 0 1 ω = "1" := by
            simp [K5Bridge.Model.blockString, h]
            native_decide
          have h11' : Is01String ("1" : String) := Is01String.of_mem_allowedWords (L := 1) (s := "1") h11
          exact (mem_cylStr_iff_blockString_eq (a := 0) ("1" : String) ω h11').2 (by simpa using hb)

  have hunion :
      FiniteDependence.MIS.Model.prob μ (cylStr (a := 0) ("0" : String) ∪ cylStr (a := 0) ("1" : String)) =
        FiniteDependence.MIS.Model.prob μ (cylStr (a := 0) ("0" : String)) +
          FiniteDependence.MIS.Model.prob μ (cylStr (a := 0) ("1" : String)) := by
    simpa using FiniteDependence.MIS.Model.prob_union (μ := μ) (s := cylStr (a := 0) ("0" : String))
      (t := cylStr (a := 0) ("1" : String)) hdisj (measurableSet_cylStr (a := 0) (s := "1"))
  have hprobUniv : FiniteDependence.MIS.Model.prob μ (univ : Set FiniteDependence.MIS.State) = 1 :=
    FiniteDependence.MIS.Model.prob_univ (μ := μ)
  have : (1 : ℝ) =
      FiniteDependence.MIS.Model.prob μ (cylStr (a := 0) ("0" : String)) +
        FiniteDependence.MIS.Model.prob μ (cylStr (a := 0) ("1" : String)) := by
    have huniv : FiniteDependence.MIS.Model.prob μ
        (cylStr (a := 0) ("0" : String) ∪ cylStr (a := 0) ("1" : String)) = 1 := by
      calc
        FiniteDependence.MIS.Model.prob μ
            (cylStr (a := 0) ("0" : String) ∪ cylStr (a := 0) ("1" : String)) =
            FiniteDependence.MIS.Model.prob μ (univ : Set FiniteDependence.MIS.State) := by
              simpa [hcover]
        _ = 1 := hprobUniv
    -- Convert `P(union)=1` and `P(union)=P0+P1` into `1 = P0 + P1`.
    simpa using huniv.symm.trans hunion
  linarith

/-! ### Endpoint decompositions at length 7 -/

private theorem cylStr_endpoints11_eq_union :
    (cylStr (a := (0 : ℤ)) "1" ∩ cylStr (a := (6 : ℤ)) "1") =
      ⋃ w ∈ good11, cylStr (a := (0 : ℤ)) w := by
  classical
  have h1mem : ("1" : String) ∈ K5Data.allowedWords 1 := by native_decide
  have h1_01 : Is01String ("1" : String) := Is01String.of_mem_allowedWords (L := 1) (s := "1") h1mem
  have h1_len : ("1" : String).length = 1 := length_of_mem_allowedWords (L := 1) (s := "1") h1mem

  ext ω
  constructor
  · rintro ⟨h0, h6⟩
    -- Translate endpoint cylinders to `blockString` equalities.
    have h0' : blockString 0 1 ω = "1" := by
      have := (mem_cylStr_iff_blockString_eq (a := (0 : ℤ)) ("1" : String) ω h1_01).1 h0
      simpa [h1_len] using this
    have h6' : blockString 6 1 ω = "1" := by
      have := (mem_cylStr_iff_blockString_eq (a := (6 : ℤ)) ("1" : String) ω h1_01).1 h6
      simpa [h1_len] using this

    let s : String := blockString 0 7 ω
    have hs_allowed : s ∈ K5Data.allowedWords 7 := by
      have : s ∈ (K5Data.allowedWords 7).toList := by
        simpa [s] using (K5Bridge.Model.blockString_mem_allowedWords (ω := ω) (a := (0 : ℤ)) (n := 6))
      simpa using this
    have hs_fin : s ∈ allowedWordsFinset 7 := (mem_allowedWordsFinset_iff (L := 7) (s := s)).2 hs_allowed

    have hs_prefix : prefixOf s 1 = "1" := by
      have : prefixOf (blockString 0 7 ω) 1 = blockString 0 1 ω :=
        prefixOf_blockString (ω := ω) (a := (0 : ℤ)) (L := 7) (m := 1) (by decide)
      simpa [s, h0'] using this

    have hs_last : s.toList.reverse.head? = some '1' := by
      -- `blockString 6 1 ω = "1"` forces the last bit of `blockString 0 7 ω` to be `'1'`.
      have hbit : ω.1 6 = true := by
        cases hω6 : ω.1 6 with
        | false =>
            have : ("" : String).push '0' = "1" := by
              simpa [K5Bridge.Model.blockString, hω6] using h6'
            have hne : (("" : String).push '0' : String) ≠ "1" := by native_decide
            exact False.elim (hne this)
        | true =>
            simpa using hω6
      have hs_push : s = (blockString 0 6 ω).push '1' := by
        simp [s, K5Bridge.Model.blockString, hbit]
      simp [hs_push, String.toList_push]
    have hs_good : s ∈ good11 := by
      have : s ∈ allowedWordsFinset 7 ∧ (prefixOf s 1 = "1" ∧ s.toList.reverse.head? = some '1') := by
        exact ⟨hs_fin, ⟨hs_prefix, hs_last⟩⟩
      simpa [good11, Finset.mem_filter] using this

    have hs01 : Is01String s := Is01String.of_mem_allowedWords (L := 7) (s := s) hs_allowed
    have hsLen : s.length = 7 := by
      simpa [s] using (K5Bridge.Model.blockString_length (a := (0 : ℤ)) (n := 7) (ω := ω))
    have hωs : ω ∈ cylStr (a := (0 : ℤ)) s := by
      have : blockString 0 s.length ω = s := by simpa [s, hsLen]
      exact (mem_cylStr_iff_blockString_eq (a := (0 : ℤ)) s ω hs01).2 this

    exact mem_iUnion.2 ⟨s, mem_iUnion.2 ⟨hs_good, hωs⟩⟩
  · intro hω
    rcases mem_iUnion.1 hω with ⟨w, hw⟩
    rcases mem_iUnion.1 hw with ⟨hwG, hωw⟩
    have hw0 : w ∈ allowedWordsFinset 7 := Finset.mem_of_mem_filter w hwG
    have hw_allowed : w ∈ K5Data.allowedWords 7 := (mem_allowedWordsFinset_iff (L := 7) (s := w)).1 hw0
    have hw01 : Is01String w := Is01String.of_mem_allowedWords (L := 7) (s := w) hw_allowed
    have hwLen : w.length = 7 := length_of_mem_allowedWords (L := 7) (s := w) hw_allowed

    have hbs : blockString 0 7 ω = w := by
      have := (mem_cylStr_iff_blockString_eq (a := (0 : ℤ)) w ω hw01).1 hωw
      simpa [hwLen] using this

    -- Reduce `w` to the two explicit possibilities.
    have hw_cases : w = "1001001" ∨ w = "1010101" := by
      have : w ∈ ({"1001001", "1010101"} : Finset String) := by simpa [good11_eq] using hwG
      simpa [Finset.mem_insert, Finset.mem_singleton] using this
    rcases hw_cases with rfl | rfl
    · -- w = 1001001
      have h0 : ω ∈ cylStr (a := (0 : ℤ)) ("1" : String) := by
        have : prefixOf (blockString 0 7 ω) 1 = blockString 0 1 ω :=
          prefixOf_blockString (ω := ω) (a := (0 : ℤ)) (L := 7) (m := 1) (by decide)
        have hx : blockString 0 1 ω = "1" := by
          simpa [hbs] using this.symm
        exact (mem_cylStr_iff_blockString_eq (a := (0 : ℤ)) ("1" : String) ω h1_01).2 (by simpa [h1_len] using hx)
      have h6 : ω ∈ cylStr (a := (6 : ℤ)) ("1" : String) := by
        have hdrop : String.ofList ((blockString 0 (6 + 1) ω).toList.drop 6) = blockString (0 + 6) 1 ω := by
          simpa using (ofList_drop_blockString_add (ω := ω) (a := (0 : ℤ)) (m := 6) (n := 1))
        have hx : blockString 6 1 ω = String.ofList ("1001001".toList.drop 6) := by
          have : String.ofList ((blockString 0 7 ω).toList.drop 6) = blockString 6 1 ω := by
            simpa [Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using hdrop
          simpa [hbs] using this.symm
        have : String.ofList ("1001001".toList.drop 6) = "1" := by native_decide
        have hx' : blockString 6 1 ω = "1" := by simpa [this] using hx
        exact (mem_cylStr_iff_blockString_eq (a := (6 : ℤ)) ("1" : String) ω h1_01).2 (by simpa [h1_len] using hx')
      exact ⟨h0, h6⟩
    · -- w = 1010101
      have h0 : ω ∈ cylStr (a := (0 : ℤ)) ("1" : String) := by
        have : prefixOf (blockString 0 7 ω) 1 = blockString 0 1 ω :=
          prefixOf_blockString (ω := ω) (a := (0 : ℤ)) (L := 7) (m := 1) (by decide)
        have hx : blockString 0 1 ω = "1" := by
          simpa [hbs] using this.symm
        exact (mem_cylStr_iff_blockString_eq (a := (0 : ℤ)) ("1" : String) ω h1_01).2 (by simpa [h1_len] using hx)
      have h6 : ω ∈ cylStr (a := (6 : ℤ)) ("1" : String) := by
        have hdrop : String.ofList ((blockString 0 (6 + 1) ω).toList.drop 6) = blockString (0 + 6) 1 ω := by
          simpa using (ofList_drop_blockString_add (ω := ω) (a := (0 : ℤ)) (m := 6) (n := 1))
        have hx : blockString 6 1 ω = String.ofList ("1010101".toList.drop 6) := by
          have : String.ofList ((blockString 0 7 ω).toList.drop 6) = blockString 6 1 ω := by
            simpa [Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using hdrop
          simpa [hbs] using this.symm
        have : String.ofList ("1010101".toList.drop 6) = "1" := by native_decide
        have hx' : blockString 6 1 ω = "1" := by simpa [this] using hx
        exact (mem_cylStr_iff_blockString_eq (a := (6 : ℤ)) ("1" : String) ω h1_01).2 (by simpa [h1_len] using hx')
      exact ⟨h0, h6⟩

private theorem cylStr_endpoints00_eq_union :
    (cylStr (a := (0 : ℤ)) "0" ∩ cylStr (a := (6 : ℤ)) "0") =
      ⋃ w ∈ good00, cylStr (a := (0 : ℤ)) w := by
  classical
  have h0mem : ("0" : String) ∈ K5Data.allowedWords 1 := by native_decide
  have h0_01 : Is01String ("0" : String) := Is01String.of_mem_allowedWords (L := 1) (s := "0") h0mem
  have h0_len : ("0" : String).length = 1 := length_of_mem_allowedWords (L := 1) (s := "0") h0mem
  ext ω
  constructor
  · rintro ⟨h0, h6⟩
    have h0' : blockString 0 1 ω = "0" := by
      have := (mem_cylStr_iff_blockString_eq (a := (0 : ℤ)) ("0" : String) ω h0_01).1 h0
      simpa [h0_len] using this
    have h6' : blockString 6 1 ω = "0" := by
      have := (mem_cylStr_iff_blockString_eq (a := (6 : ℤ)) ("0" : String) ω h0_01).1 h6
      simpa [h0_len] using this
    let s : String := blockString 0 7 ω
    have hs_allowed : s ∈ K5Data.allowedWords 7 := by
      have : s ∈ (K5Data.allowedWords 7).toList := by
        simpa [s] using (K5Bridge.Model.blockString_mem_allowedWords (ω := ω) (a := (0 : ℤ)) (n := 6))
      simpa using this
    have hs_fin : s ∈ allowedWordsFinset 7 := (mem_allowedWordsFinset_iff (L := 7) (s := s)).2 hs_allowed
    have hs_prefix : prefixOf s 1 = "0" := by
      have : prefixOf (blockString 0 7 ω) 1 = blockString 0 1 ω :=
        prefixOf_blockString (ω := ω) (a := (0 : ℤ)) (L := 7) (m := 1) (by decide)
      simpa [s, h0'] using this
    have hs_last : s.toList.reverse.head? = some '0' := by
      have hbit : ω.1 6 = false := by
        cases hω6 : ω.1 6 with
        | false => simpa using hω6
        | true =>
            have : ("" : String).push '1' = "0" := by
              simpa [K5Bridge.Model.blockString, hω6] using h6'
            have hne : (("" : String).push '1' : String) ≠ "0" := by native_decide
            exact False.elim (hne this)
      have hs_push : s = (blockString 0 6 ω).push '0' := by
        simp [s, K5Bridge.Model.blockString, hbit]
      simp [hs_push, String.toList_push]
    have hs_good : s ∈ good00 := by
      have : s ∈ allowedWordsFinset 7 ∧ (prefixOf s 1 = "0" ∧ s.toList.reverse.head? = some '0') := by
        exact ⟨hs_fin, ⟨hs_prefix, hs_last⟩⟩
      simpa [good00, Finset.mem_filter] using this
    have hs01 : Is01String s := Is01String.of_mem_allowedWords (L := 7) (s := s) hs_allowed
    have hsLen : s.length = 7 := by
      simpa [s] using (K5Bridge.Model.blockString_length (a := (0 : ℤ)) (n := 7) (ω := ω))
    have hωs : ω ∈ cylStr (a := (0 : ℤ)) s := by
      have : blockString 0 s.length ω = s := by simpa [s, hsLen]
      exact (mem_cylStr_iff_blockString_eq (a := (0 : ℤ)) s ω hs01).2 this
    exact mem_iUnion.2 ⟨s, mem_iUnion.2 ⟨hs_good, hωs⟩⟩
  · intro hω
    rcases mem_iUnion.1 hω with ⟨w, hw⟩
    rcases mem_iUnion.1 hw with ⟨hwG, hωw⟩
    have hw_cases : w = "0010010" ∨ w = "0010100" ∨ w = "0100100" ∨ w = "0101010" := by
      have : w ∈ ({"0010010", "0010100", "0100100", "0101010"} : Finset String) := by
        simpa [good00_eq] using hwG
      simpa [Finset.mem_insert, Finset.mem_singleton, or_assoc, or_left_comm, or_comm] using this
    rcases hw_cases with rfl | rfl | rfl | rfl
    · -- w = 0010010
      have hbs : blockString 0 7 ω = ("0010010" : String) := by
        have hw7 : ("0010010" : String) ∈ K5Data.allowedWords 7 := by native_decide
        have w7 : Is01String ("0010010" : String) := Is01String.of_mem_allowedWords (L := 7) (s := "0010010") hw7
        have := (mem_cylStr_iff_blockString_eq (a := (0 : ℤ)) ("0010010" : String) ω w7).1 hωw
        simpa using this
      have h0 : ω ∈ cylStr (a := (0 : ℤ)) ("0" : String) := by
        have : prefixOf (blockString 0 7 ω) 1 = blockString 0 1 ω :=
          prefixOf_blockString (ω := ω) (a := (0 : ℤ)) (L := 7) (m := 1) (by decide)
        have hprefix : prefixOf ("0010010" : String) 1 = "0" := by native_decide
        have hx : blockString 0 1 ω = "0" := by simpa [hbs, hprefix] using this.symm
        exact (mem_cylStr_iff_blockString_eq (a := (0 : ℤ)) ("0" : String) ω h0_01).2 (by simpa [h0_len] using hx)
      have h6 : ω ∈ cylStr (a := (6 : ℤ)) ("0" : String) := by
        have hdrop : String.ofList ((blockString 0 (6 + 1) ω).toList.drop 6) = blockString (0 + 6) 1 ω := by
          simpa using (ofList_drop_blockString_add (ω := ω) (a := (0 : ℤ)) (m := 6) (n := 1))
        have hx : blockString 6 1 ω = String.ofList ("0010010".toList.drop 6) := by
          have : String.ofList ((blockString 0 7 ω).toList.drop 6) = blockString 6 1 ω := by
            simpa [Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using hdrop
          simpa [hbs] using this.symm
        have : String.ofList ("0010010".toList.drop 6) = "0" := by native_decide
        have hx' : blockString 6 1 ω = "0" := by simpa [this] using hx
        exact (mem_cylStr_iff_blockString_eq (a := (6 : ℤ)) ("0" : String) ω h0_01).2 (by simpa [h0_len] using hx')
      exact ⟨h0, h6⟩
    · -- w = 0010100
      have hbs : blockString 0 7 ω = ("0010100" : String) := by
        have hw7 : ("0010100" : String) ∈ K5Data.allowedWords 7 := by native_decide
        have w7 : Is01String ("0010100" : String) := Is01String.of_mem_allowedWords (L := 7) (s := "0010100") hw7
        have := (mem_cylStr_iff_blockString_eq (a := (0 : ℤ)) ("0010100" : String) ω w7).1 hωw
        simpa using this
      have h0 : ω ∈ cylStr (a := (0 : ℤ)) ("0" : String) := by
        have : prefixOf (blockString 0 7 ω) 1 = blockString 0 1 ω :=
          prefixOf_blockString (ω := ω) (a := (0 : ℤ)) (L := 7) (m := 1) (by decide)
        have hprefix : prefixOf ("0010100" : String) 1 = "0" := by native_decide
        have hx : blockString 0 1 ω = "0" := by simpa [hbs, hprefix] using this.symm
        exact (mem_cylStr_iff_blockString_eq (a := (0 : ℤ)) ("0" : String) ω h0_01).2 (by simpa [h0_len] using hx)
      have h6 : ω ∈ cylStr (a := (6 : ℤ)) ("0" : String) := by
        have hdrop : String.ofList ((blockString 0 (6 + 1) ω).toList.drop 6) = blockString (0 + 6) 1 ω := by
          simpa using (ofList_drop_blockString_add (ω := ω) (a := (0 : ℤ)) (m := 6) (n := 1))
        have hx : blockString 6 1 ω = String.ofList ("0010100".toList.drop 6) := by
          have : String.ofList ((blockString 0 7 ω).toList.drop 6) = blockString 6 1 ω := by
            simpa [Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using hdrop
          simpa [hbs] using this.symm
        have : String.ofList ("0010100".toList.drop 6) = "0" := by native_decide
        have hx' : blockString 6 1 ω = "0" := by simpa [this] using hx
        exact (mem_cylStr_iff_blockString_eq (a := (6 : ℤ)) ("0" : String) ω h0_01).2 (by simpa [h0_len] using hx')
      exact ⟨h0, h6⟩
    · -- w = 0100100
      have hbs : blockString 0 7 ω = ("0100100" : String) := by
        have hw7 : ("0100100" : String) ∈ K5Data.allowedWords 7 := by native_decide
        have w7 : Is01String ("0100100" : String) := Is01String.of_mem_allowedWords (L := 7) (s := "0100100") hw7
        have := (mem_cylStr_iff_blockString_eq (a := (0 : ℤ)) ("0100100" : String) ω w7).1 hωw
        simpa using this
      have h0 : ω ∈ cylStr (a := (0 : ℤ)) ("0" : String) := by
        have : prefixOf (blockString 0 7 ω) 1 = blockString 0 1 ω :=
          prefixOf_blockString (ω := ω) (a := (0 : ℤ)) (L := 7) (m := 1) (by decide)
        have hprefix : prefixOf ("0100100" : String) 1 = "0" := by native_decide
        have hx : blockString 0 1 ω = "0" := by simpa [hbs, hprefix] using this.symm
        exact (mem_cylStr_iff_blockString_eq (a := (0 : ℤ)) ("0" : String) ω h0_01).2 (by simpa [h0_len] using hx)
      have h6 : ω ∈ cylStr (a := (6 : ℤ)) ("0" : String) := by
        have hdrop : String.ofList ((blockString 0 (6 + 1) ω).toList.drop 6) = blockString (0 + 6) 1 ω := by
          simpa using (ofList_drop_blockString_add (ω := ω) (a := (0 : ℤ)) (m := 6) (n := 1))
        have hx : blockString 6 1 ω = String.ofList ("0100100".toList.drop 6) := by
          have : String.ofList ((blockString 0 7 ω).toList.drop 6) = blockString 6 1 ω := by
            simpa [Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using hdrop
          simpa [hbs] using this.symm
        have : String.ofList ("0100100".toList.drop 6) = "0" := by native_decide
        have hx' : blockString 6 1 ω = "0" := by simpa [this] using hx
        exact (mem_cylStr_iff_blockString_eq (a := (6 : ℤ)) ("0" : String) ω h0_01).2 (by simpa [h0_len] using hx')
      exact ⟨h0, h6⟩
    · -- w = 0101010
      have hbs : blockString 0 7 ω = ("0101010" : String) := by
        have hw7 : ("0101010" : String) ∈ K5Data.allowedWords 7 := by native_decide
        have w7 : Is01String ("0101010" : String) := Is01String.of_mem_allowedWords (L := 7) (s := "0101010") hw7
        have := (mem_cylStr_iff_blockString_eq (a := (0 : ℤ)) ("0101010" : String) ω w7).1 hωw
        simpa using this
      have h0 : ω ∈ cylStr (a := (0 : ℤ)) ("0" : String) := by
        have : prefixOf (blockString 0 7 ω) 1 = blockString 0 1 ω :=
          prefixOf_blockString (ω := ω) (a := (0 : ℤ)) (L := 7) (m := 1) (by decide)
        have hprefix : prefixOf ("0101010" : String) 1 = "0" := by native_decide
        have hx : blockString 0 1 ω = "0" := by simpa [hbs, hprefix] using this.symm
        exact (mem_cylStr_iff_blockString_eq (a := (0 : ℤ)) ("0" : String) ω h0_01).2 (by simpa [h0_len] using hx)
      have h6 : ω ∈ cylStr (a := (6 : ℤ)) ("0" : String) := by
        have hdrop : String.ofList ((blockString 0 (6 + 1) ω).toList.drop 6) = blockString (0 + 6) 1 ω := by
          simpa using (ofList_drop_blockString_add (ω := ω) (a := (0 : ℤ)) (m := 6) (n := 1))
        have hx : blockString 6 1 ω = String.ofList ("0101010".toList.drop 6) := by
          have : String.ofList ((blockString 0 7 ω).toList.drop 6) = blockString 6 1 ω := by
            simpa [Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using hdrop
          simpa [hbs] using this.symm
        have : String.ofList ("0101010".toList.drop 6) = "0" := by native_decide
        have hx' : blockString 6 1 ω = "0" := by simpa [this] using hx
        exact (mem_cylStr_iff_blockString_eq (a := (6 : ℤ)) ("0" : String) ω h0_01).2 (by simpa [h0_len] using hx')
      exact ⟨h0, h6⟩

private theorem cylStr_endpoints01_eq_union :
    (cylStr (a := (0 : ℤ)) "0" ∩ cylStr (a := (6 : ℤ)) "1") =
      ⋃ w ∈ good01, cylStr (a := (0 : ℤ)) w := by
  classical
  have h0mem : ("0" : String) ∈ K5Data.allowedWords 1 := by native_decide
  have h1mem : ("1" : String) ∈ K5Data.allowedWords 1 := by native_decide
  have h0_01 : Is01String ("0" : String) := Is01String.of_mem_allowedWords (L := 1) (s := "0") h0mem
  have h1_01 : Is01String ("1" : String) := Is01String.of_mem_allowedWords (L := 1) (s := "1") h1mem
  have h0_len : ("0" : String).length = 1 := length_of_mem_allowedWords (L := 1) (s := "0") h0mem
  have h1_len : ("1" : String).length = 1 := length_of_mem_allowedWords (L := 1) (s := "1") h1mem
  ext ω
  constructor
  · rintro ⟨h0, h6⟩
    have h0' : blockString 0 1 ω = "0" := by
      have := (mem_cylStr_iff_blockString_eq (a := (0 : ℤ)) ("0" : String) ω h0_01).1 h0
      simpa [h0_len] using this
    have h6' : blockString 6 1 ω = "1" := by
      have := (mem_cylStr_iff_blockString_eq (a := (6 : ℤ)) ("1" : String) ω h1_01).1 h6
      simpa [h1_len] using this
    let s : String := blockString 0 7 ω
    have hs_allowed : s ∈ K5Data.allowedWords 7 := by
      have : s ∈ (K5Data.allowedWords 7).toList := by
        simpa [s] using (K5Bridge.Model.blockString_mem_allowedWords (ω := ω) (a := (0 : ℤ)) (n := 6))
      simpa using this
    have hs_fin : s ∈ allowedWordsFinset 7 := (mem_allowedWordsFinset_iff (L := 7) (s := s)).2 hs_allowed
    have hs_prefix : prefixOf s 1 = "0" := by
      have : prefixOf (blockString 0 7 ω) 1 = blockString 0 1 ω :=
        prefixOf_blockString (ω := ω) (a := (0 : ℤ)) (L := 7) (m := 1) (by decide)
      simpa [s, h0'] using this
    have hs_last : s.toList.reverse.head? = some '1' := by
      have hbit : ω.1 6 = true := by
        cases hω6 : ω.1 6 with
        | false =>
            have : ("" : String).push '0' = "1" := by
              simpa [K5Bridge.Model.blockString, hω6] using h6'
            have hne : (("" : String).push '0' : String) ≠ "1" := by native_decide
            exact False.elim (hne this)
        | true => simpa using hω6
      have hs_push : s = (blockString 0 6 ω).push '1' := by
        simp [s, K5Bridge.Model.blockString, hbit]
      simp [hs_push, String.toList_push]
    have hs_good : s ∈ good01 := by
      have : s ∈ allowedWordsFinset 7 ∧ (prefixOf s 1 = "0" ∧ s.toList.reverse.head? = some '1') := by
        exact ⟨hs_fin, ⟨hs_prefix, hs_last⟩⟩
      simpa [good01, Finset.mem_filter] using this
    have hs01 : Is01String s := Is01String.of_mem_allowedWords (L := 7) (s := s) hs_allowed
    have hsLen : s.length = 7 := by
      simpa [s] using (K5Bridge.Model.blockString_length (a := (0 : ℤ)) (n := 7) (ω := ω))
    have hωs : ω ∈ cylStr (a := (0 : ℤ)) s := by
      have : blockString 0 s.length ω = s := by simpa [s, hsLen]
      exact (mem_cylStr_iff_blockString_eq (a := (0 : ℤ)) s ω hs01).2 this
    exact mem_iUnion.2 ⟨s, mem_iUnion.2 ⟨hs_good, hωs⟩⟩
  · intro hω
    rcases mem_iUnion.1 hω with ⟨w, hw⟩
    rcases mem_iUnion.1 hw with ⟨hwG, hωw⟩
    have hw_cases : w = "0010101" ∨ w = "0100101" ∨ w = "0101001" := by
      have : w ∈ ({"0010101", "0100101", "0101001"} : Finset String) := by
        simpa [good01_eq] using hwG
      simpa [Finset.mem_insert, Finset.mem_singleton, or_assoc, or_left_comm, or_comm] using this
    rcases hw_cases with rfl | rfl | rfl
    · -- w = 0010101
      have hbs : blockString 0 7 ω = ("0010101" : String) := by
        have hw7 : ("0010101" : String) ∈ K5Data.allowedWords 7 := by native_decide
        have w7 : Is01String ("0010101" : String) := Is01String.of_mem_allowedWords (L := 7) (s := "0010101") hw7
        have := (mem_cylStr_iff_blockString_eq (a := (0 : ℤ)) ("0010101" : String) ω w7).1 hωw
        simpa using this
      have h0 : ω ∈ cylStr (a := (0 : ℤ)) ("0" : String) := by
        have : prefixOf (blockString 0 7 ω) 1 = blockString 0 1 ω :=
          prefixOf_blockString (ω := ω) (a := (0 : ℤ)) (L := 7) (m := 1) (by decide)
        have hprefix : prefixOf ("0010101" : String) 1 = "0" := by native_decide
        have hx : blockString 0 1 ω = "0" := by simpa [hbs, hprefix] using this.symm
        exact (mem_cylStr_iff_blockString_eq (a := (0 : ℤ)) ("0" : String) ω h0_01).2 (by simpa [h0_len] using hx)
      have h6 : ω ∈ cylStr (a := (6 : ℤ)) ("1" : String) := by
        have hdrop : String.ofList ((blockString 0 (6 + 1) ω).toList.drop 6) = blockString (0 + 6) 1 ω := by
          simpa using (ofList_drop_blockString_add (ω := ω) (a := (0 : ℤ)) (m := 6) (n := 1))
        have hx : blockString 6 1 ω = String.ofList ("0010101".toList.drop 6) := by
          have : String.ofList ((blockString 0 7 ω).toList.drop 6) = blockString 6 1 ω := by
            simpa [Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using hdrop
          simpa [hbs] using this.symm
        have : String.ofList ("0010101".toList.drop 6) = "1" := by native_decide
        have hx' : blockString 6 1 ω = "1" := by simpa [this] using hx
        exact (mem_cylStr_iff_blockString_eq (a := (6 : ℤ)) ("1" : String) ω h1_01).2 (by simpa [h1_len] using hx')
      exact ⟨h0, h6⟩
    · -- w = 0100101
      have hbs : blockString 0 7 ω = ("0100101" : String) := by
        have hw7 : ("0100101" : String) ∈ K5Data.allowedWords 7 := by native_decide
        have w7 : Is01String ("0100101" : String) := Is01String.of_mem_allowedWords (L := 7) (s := "0100101") hw7
        have := (mem_cylStr_iff_blockString_eq (a := (0 : ℤ)) ("0100101" : String) ω w7).1 hωw
        simpa using this
      have h0 : ω ∈ cylStr (a := (0 : ℤ)) ("0" : String) := by
        have : prefixOf (blockString 0 7 ω) 1 = blockString 0 1 ω :=
          prefixOf_blockString (ω := ω) (a := (0 : ℤ)) (L := 7) (m := 1) (by decide)
        have hprefix : prefixOf ("0100101" : String) 1 = "0" := by native_decide
        have hx : blockString 0 1 ω = "0" := by simpa [hbs, hprefix] using this.symm
        exact (mem_cylStr_iff_blockString_eq (a := (0 : ℤ)) ("0" : String) ω h0_01).2 (by simpa [h0_len] using hx)
      have h6 : ω ∈ cylStr (a := (6 : ℤ)) ("1" : String) := by
        have hdrop : String.ofList ((blockString 0 (6 + 1) ω).toList.drop 6) = blockString (0 + 6) 1 ω := by
          simpa using (ofList_drop_blockString_add (ω := ω) (a := (0 : ℤ)) (m := 6) (n := 1))
        have hx : blockString 6 1 ω = String.ofList ("0100101".toList.drop 6) := by
          have : String.ofList ((blockString 0 7 ω).toList.drop 6) = blockString 6 1 ω := by
            simpa [Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using hdrop
          simpa [hbs] using this.symm
        have : String.ofList ("0100101".toList.drop 6) = "1" := by native_decide
        have hx' : blockString 6 1 ω = "1" := by simpa [this] using hx
        exact (mem_cylStr_iff_blockString_eq (a := (6 : ℤ)) ("1" : String) ω h1_01).2 (by simpa [h1_len] using hx')
      exact ⟨h0, h6⟩
    · -- w = 0101001
      have hbs : blockString 0 7 ω = ("0101001" : String) := by
        have hw7 : ("0101001" : String) ∈ K5Data.allowedWords 7 := by native_decide
        have w7 : Is01String ("0101001" : String) := Is01String.of_mem_allowedWords (L := 7) (s := "0101001") hw7
        have := (mem_cylStr_iff_blockString_eq (a := (0 : ℤ)) ("0101001" : String) ω w7).1 hωw
        simpa using this
      have h0 : ω ∈ cylStr (a := (0 : ℤ)) ("0" : String) := by
        have : prefixOf (blockString 0 7 ω) 1 = blockString 0 1 ω :=
          prefixOf_blockString (ω := ω) (a := (0 : ℤ)) (L := 7) (m := 1) (by decide)
        have hprefix : prefixOf ("0101001" : String) 1 = "0" := by native_decide
        have hx : blockString 0 1 ω = "0" := by simpa [hbs, hprefix] using this.symm
        exact (mem_cylStr_iff_blockString_eq (a := (0 : ℤ)) ("0" : String) ω h0_01).2 (by simpa [h0_len] using hx)
      have h6 : ω ∈ cylStr (a := (6 : ℤ)) ("1" : String) := by
        have hdrop : String.ofList ((blockString 0 (6 + 1) ω).toList.drop 6) = blockString (0 + 6) 1 ω := by
          simpa using (ofList_drop_blockString_add (ω := ω) (a := (0 : ℤ)) (m := 6) (n := 1))
        have hx : blockString 6 1 ω = String.ofList ("0101001".toList.drop 6) := by
          have : String.ofList ((blockString 0 7 ω).toList.drop 6) = blockString 6 1 ω := by
            simpa [Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using hdrop
          simpa [hbs] using this.symm
        have : String.ofList ("0101001".toList.drop 6) = "1" := by native_decide
        have hx' : blockString 6 1 ω = "1" := by simpa [this] using hx
        exact (mem_cylStr_iff_blockString_eq (a := (6 : ℤ)) ("1" : String) ω h1_01).2 (by simpa [h1_len] using hx')
      exact ⟨h0, h6⟩

/-! ### Main formulas -/

theorem prob_dist7_formulas (μ : Measure FiniteDependence.MIS.State) [IsProbabilityMeasure μ]
    (hstat : Stationary μ) (hdep : KDependent 5 μ) :
    let p : ℝ := FiniteDependence.MIS.Model.prob μ (cylStr (a := 0) "1")
    let t : ℝ := FiniteDependence.MIS.Model.prob μ (cylStr (a := 0) "1010101")
    FiniteDependence.MIS.Model.prob μ (cylStr (a := 0) "0010010") = p ^ 2 - t ∧
    FiniteDependence.MIS.Model.prob μ (cylStr (a := 0) "0010100") =
        (-2) * p ^ 2 + (-7) * p + 3 * t + 3 ∧
    FiniteDependence.MIS.Model.prob μ (cylStr (a := 0) "0010101") =
        p ^ 2 + 5 * p - 2 * t - 2 ∧
    FiniteDependence.MIS.Model.prob μ (cylStr (a := 0) "0100100") = p ^ 2 - t ∧
    FiniteDependence.MIS.Model.prob μ (cylStr (a := 0) "0100101") =
        (-1) * p ^ 2 + (-2) * p + t + 1 ∧
    FiniteDependence.MIS.Model.prob μ (cylStr (a := 0) "0101001") =
        (-1) * p ^ 2 + (-2) * p + t + 1 ∧
    FiniteDependence.MIS.Model.prob μ (cylStr (a := 0) "0101010") =
        p ^ 2 + 5 * p - t - 2 ∧
    FiniteDependence.MIS.Model.prob μ (cylStr (a := 0) "1001001") = p ^ 2 - t ∧
    FiniteDependence.MIS.Model.prob μ (cylStr (a := 0) "1001010") =
        (-1) * p ^ 2 + (-2) * p + t + 1 ∧
    FiniteDependence.MIS.Model.prob μ (cylStr (a := 0) "1010010") =
        (-1) * p ^ 2 + (-2) * p + t + 1 ∧
    FiniteDependence.MIS.Model.prob μ (cylStr (a := 0) "1010100") =
        p ^ 2 + 5 * p - 2 * t - 2 ∧
    FiniteDependence.MIS.Model.prob μ (cylStr (a := 0) "1010101") = t := by
  classical
  -- Parameters.
  set p : ℝ := FiniteDependence.MIS.Model.prob μ (cylStr (a := 0) "1")
  set t : ℝ := FiniteDependence.MIS.Model.prob μ (cylStr (a := 0) "1010101")

  -- Length-6 stationarity equations as equalities of length-7 sums.
  have st6 (u : String) (hu : u ∈ K5Data.allowedWords 6) :
      (∑ w ∈ pref6 u, FiniteDependence.MIS.Model.prob μ (cylStr (a := (0 : ℤ)) w)) =
        ∑ w ∈ suf6 u, FiniteDependence.MIS.Model.prob μ (cylStr (a := (0 : ℤ)) w) := by
    have hu01 : Is01String u := Is01String.of_mem_allowedWords (L := 6) (s := u) hu
    have huLen : u.length = 6 := length_of_mem_allowedWords (L := 6) (s := u) hu
    have hpref :
        FiniteDependence.MIS.Model.prob μ (cylStr (a := (0 : ℤ)) u) =
          ∑ w ∈ pref6 u, FiniteDependence.MIS.Model.prob μ (cylStr (a := (0 : ℤ)) w) := by
      simpa [pref6] using
        (prob_prefix_eq_sum (μ := μ) (a := (0 : ℤ)) (L := 7) (m := 6) (hL := by decide) (hm := by decide)
          (x := u) hu01 huLen)
    have hsuf :
        FiniteDependence.MIS.Model.prob μ (cylStr (a := (0 : ℤ) + 1) u) =
          ∑ w ∈ suf6 u, FiniteDependence.MIS.Model.prob μ (cylStr (a := (0 : ℤ)) w) := by
      simpa [suf6] using (prob_suffix1_eq_sum (μ := μ) (a := (0 : ℤ)) (m := 6) (x := u) hu01 huLen)
    have hshift :
        FiniteDependence.MIS.Model.prob μ (cylStr (a := (0 : ℤ) + 1) u) =
          FiniteDependence.MIS.Model.prob μ (cylStr (a := (0 : ℤ)) u) := by
      simpa using (Stationary.prob_cylStr_succ (μ := μ) hstat (a := (0 : ℤ)) (s := u))
    -- Put together.
    linarith [hpref, hsuf, hshift]

  -- Extract the particular length-6 stationarity relations we need.
  have h001001 : FiniteDependence.MIS.Model.prob μ (cylStr (a := 0) "0010010") =
      FiniteDependence.MIS.Model.prob μ (cylStr (a := 0) "1001001") := by
    have hu : ("001001" : String) ∈ K5Data.allowedWords 6 := by native_decide
    have h := st6 "001001" hu
    rw [pref6_001001, suf6_001001] at h
    simpa using h

  have h100100 : FiniteDependence.MIS.Model.prob μ (cylStr (a := 0) "1001001") =
      FiniteDependence.MIS.Model.prob μ (cylStr (a := 0) "0100100") := by
    have hu : ("100100" : String) ∈ K5Data.allowedWords 6 := by native_decide
    have h := st6 "100100" hu
    rw [pref6_100100, suf6_100100] at h
    simpa using h

  have h001010 : FiniteDependence.MIS.Model.prob μ (cylStr (a := 0) "0010100") +
      FiniteDependence.MIS.Model.prob μ (cylStr (a := 0) "0010101") =
        FiniteDependence.MIS.Model.prob μ (cylStr (a := 0) "1001010") := by
    have hu : ("001010" : String) ∈ K5Data.allowedWords 6 := by native_decide
    have h := st6 "001010" hu
    rw [pref6_001010, suf6_001010] at h
    simpa [add_comm, add_left_comm, add_assoc] using h

  have h100101 : FiniteDependence.MIS.Model.prob μ (cylStr (a := 0) "1001010") =
      FiniteDependence.MIS.Model.prob μ (cylStr (a := 0) "0100101") := by
    have hu : ("100101" : String) ∈ K5Data.allowedWords 6 := by native_decide
    have h := st6 "100101" hu
    rw [pref6_100101, suf6_100101] at h
    simpa using h

  have h010010 : FiniteDependence.MIS.Model.prob μ (cylStr (a := 0) "0100100") +
      FiniteDependence.MIS.Model.prob μ (cylStr (a := 0) "0100101") =
        FiniteDependence.MIS.Model.prob μ (cylStr (a := 0) "0010010") +
          FiniteDependence.MIS.Model.prob μ (cylStr (a := 0) "1010010") := by
    have hu : ("010010" : String) ∈ K5Data.allowedWords 6 := by native_decide
    have h := st6 "010010" hu
    rw [pref6_010010, suf6_010010] at h
    simpa [add_comm, add_left_comm, add_assoc] using h

  have h010100 : FiniteDependence.MIS.Model.prob μ (cylStr (a := 0) "0101001") =
      FiniteDependence.MIS.Model.prob μ (cylStr (a := 0) "0010100") +
        FiniteDependence.MIS.Model.prob μ (cylStr (a := 0) "1010100") := by
    have hu : ("010100" : String) ∈ K5Data.allowedWords 6 := by native_decide
    have h := st6 "010100" hu
    rw [pref6_010100, suf6_010100] at h
    simpa [add_comm, add_left_comm, add_assoc] using h

  have h101001 : FiniteDependence.MIS.Model.prob μ (cylStr (a := 0) "1010010") =
      FiniteDependence.MIS.Model.prob μ (cylStr (a := 0) "0101001") := by
    have hu : ("101001" : String) ∈ K5Data.allowedWords 6 := by native_decide
    have h := st6 "101001" hu
    rw [pref6_101001, suf6_101001] at h
    simpa using h

  have h010101 : FiniteDependence.MIS.Model.prob μ (cylStr (a := 0) "0101010") =
      FiniteDependence.MIS.Model.prob μ (cylStr (a := 0) "0010101") +
        FiniteDependence.MIS.Model.prob μ (cylStr (a := 0) "1010101") := by
    have hu : ("010101" : String) ∈ K5Data.allowedWords 6 := by native_decide
    have h := st6 "010101" hu
    rw [pref6_010101, suf6_010101] at h
    simpa [add_comm, add_left_comm, add_assoc] using h

  have h101010 : FiniteDependence.MIS.Model.prob μ (cylStr (a := 0) "1010100") +
      FiniteDependence.MIS.Model.prob μ (cylStr (a := 0) "1010101") =
        FiniteDependence.MIS.Model.prob μ (cylStr (a := 0) "0101010") := by
    have hu : ("101010" : String) ∈ K5Data.allowedWords 6 := by native_decide
    have h := st6 "101010" hu
    rw [pref6_101010, suf6_101010] at h
    simpa [add_comm, add_left_comm, add_assoc] using h

  -- Some derived equalities among length-7 probabilities.
  have h0010010_eq_0100100 :
      FiniteDependence.MIS.Model.prob μ (cylStr (a := 0) "0010010") =
        FiniteDependence.MIS.Model.prob μ (cylStr (a := 0) "0100100") := by
    linarith [h001001, h100100]

  have h0100101_eq_0010100_add_0010101 :
      FiniteDependence.MIS.Model.prob μ (cylStr (a := 0) "0100101") =
        FiniteDependence.MIS.Model.prob μ (cylStr (a := 0) "0010100") +
          FiniteDependence.MIS.Model.prob μ (cylStr (a := 0) "0010101") := by
    linarith [h001010, h100101]

  have h0101001_eq_0100101 :
      FiniteDependence.MIS.Model.prob μ (cylStr (a := 0) "0101001") =
        FiniteDependence.MIS.Model.prob μ (cylStr (a := 0) "0100101") := by
    linarith [h010010, h0010010_eq_0100100, h101001]

  have h1010010_eq_0100101 :
      FiniteDependence.MIS.Model.prob μ (cylStr (a := 0) "1010010") =
        FiniteDependence.MIS.Model.prob μ (cylStr (a := 0) "0100101") := by
    linarith [h101001, h0101001_eq_0100101]

  have h1010100_eq_0010101 :
      FiniteDependence.MIS.Model.prob μ (cylStr (a := 0) "1010100") =
        FiniteDependence.MIS.Model.prob μ (cylStr (a := 0) "0010101") := by
    -- Compare the two ways to express `P(0101010)`:
    --   `P(0101010) = P(0010101) + P(1010101)` and
    --   `P(0101010) = P(1010100) + P(1010101)`.
    linarith [h010101, h101010]

  have h0101010_eq_0010101_add_t :
      FiniteDependence.MIS.Model.prob μ (cylStr (a := 0) "0101010") =
        FiniteDependence.MIS.Model.prob μ (cylStr (a := 0) "0010101") + t := by
    simpa [t] using h010101

  have h0100101_eq_u :
      FiniteDependence.MIS.Model.prob μ (cylStr (a := 0) "0100101") =
        FiniteDependence.MIS.Model.prob μ (cylStr (a := 0) "0010100") +
          FiniteDependence.MIS.Model.prob μ (cylStr (a := 0) "0010101") := by
    simpa [add_comm, add_left_comm, add_assoc] using h0100101_eq_0010100_add_0010101

  have h0101001_eq_u :
      FiniteDependence.MIS.Model.prob μ (cylStr (a := 0) "0101001") =
        FiniteDependence.MIS.Model.prob μ (cylStr (a := 0) "0010100") +
          FiniteDependence.MIS.Model.prob μ (cylStr (a := 0) "0010101") := by
    linarith [h0101001_eq_0100101, h0100101_eq_u]

  have h1001010_eq_u :
      FiniteDependence.MIS.Model.prob μ (cylStr (a := 0) "1001010") =
        FiniteDependence.MIS.Model.prob μ (cylStr (a := 0) "0010100") +
          FiniteDependence.MIS.Model.prob μ (cylStr (a := 0) "0010101") := by
    linarith [h100101, h0100101_eq_u]

  have h1010010_eq_u :
      FiniteDependence.MIS.Model.prob μ (cylStr (a := 0) "1010010") =
        FiniteDependence.MIS.Model.prob μ (cylStr (a := 0) "0010100") +
          FiniteDependence.MIS.Model.prob μ (cylStr (a := 0) "0010101") := by
    linarith [h1010010_eq_0100101, h0100101_eq_u]

  -- Endpoint decompositions give three linear equations.
  have hend11 :
      FiniteDependence.MIS.Model.prob μ (cylStr (a := (0 : ℤ)) "1001001") +
        FiniteDependence.MIS.Model.prob μ (cylStr (a := (0 : ℤ)) "1010101") =
          p ^ 2 := by
    have hd :
        PairwiseDisjoint (↑good11 : Set String) (fun w => cylStr (a := (0 : ℤ)) w) := by
      intro w hw u hu hwu
      have hw0 : w ∈ allowedWordsFinset 7 := Finset.mem_of_mem_filter w hw
      have hu0 : u ∈ allowedWordsFinset 7 := Finset.mem_of_mem_filter u hu
      exact pairwiseDisjoint_cylStr_allowedWords (a := (0 : ℤ)) (L := 7) hw0 hu0 hwu
    have hm : ∀ w ∈ good11, MeasurableSet (cylStr (a := (0 : ℤ)) w) := by
      intro w _hw
      simpa using measurableSet_cylStr (a := (0 : ℤ)) (s := w)
    have hprobUnion :
        FiniteDependence.MIS.Model.prob μ (⋃ w ∈ good11, cylStr (a := (0 : ℤ)) w) =
          ∑ w ∈ good11, FiniteDependence.MIS.Model.prob μ (cylStr (a := (0 : ℤ)) w) :=
      prob_biUnion_finset (μ := μ) (s := good11) (f := fun w => cylStr (a := (0 : ℤ)) w) hd hm
    have hsum :
        FiniteDependence.MIS.Model.prob μ (cylStr (a := (0 : ℤ)) "1" ∩ cylStr (a := (6 : ℤ)) "1") =
          FiniteDependence.MIS.Model.prob μ (cylStr (a := (0 : ℤ)) "1001001") +
            FiniteDependence.MIS.Model.prob μ (cylStr (a := (0 : ℤ)) "1010101") := by
      have :
          FiniteDependence.MIS.Model.prob μ (cylStr (a := (0 : ℤ)) "1" ∩ cylStr (a := (6 : ℤ)) "1") =
            ∑ w ∈ good11, FiniteDependence.MIS.Model.prob μ (cylStr (a := (0 : ℤ)) w) := by
        calc
          FiniteDependence.MIS.Model.prob μ (cylStr (a := (0 : ℤ)) "1" ∩ cylStr (a := (6 : ℤ)) "1") =
              FiniteDependence.MIS.Model.prob μ (⋃ w ∈ good11, cylStr (a := (0 : ℤ)) w) := by
                simpa [cylStr_endpoints11_eq_union]
          _ = ∑ w ∈ good11, FiniteDependence.MIS.Model.prob μ (cylStr (a := (0 : ℤ)) w) := hprobUnion
      -- Compute the small sum over `good11`.
      simpa [good11_eq, add_assoc, add_left_comm, add_comm] using this
    -- Independence at distance 6.
    have hsep :
        ∀ i : Fin 1, ∀ j : Fin 1,
          Int.natAbs ((0 + Int.ofNat i.1) - (6 + Int.ofNat j.1)) > 5 := by
      intro i j; fin_cases i <;> fin_cases j <;> simp
    have hind :
        FiniteDependence.MIS.Model.prob μ (cylStr (a := (0 : ℤ)) "1" ∩ cylStr (a := (6 : ℤ)) "1") =
          FiniteDependence.MIS.Model.prob μ (cylStr (a := (0 : ℤ)) "1") *
            FiniteDependence.MIS.Model.prob μ (cylStr (a := (6 : ℤ)) "1") := by
      simpa [cylStr] using
        (FiniteDependence.MIS.Model.KDependent.prob_inter_cyl_eq_mul (μ := μ) (k := 5)
          (m := 1) (n := 1) (a := (0 : ℤ)) (b := (6 : ℤ)) hdep hsep
          (K5Bridge.wordOfString "1") (K5Bridge.wordOfString "1"))
    have hs6p :
        FiniteDependence.MIS.Model.prob μ (cylStr (a := (6 : ℤ)) "1") = p := by
      have := prob_cylStr_add_nat (μ := μ) hstat (a := (0 : ℤ)) (s := "1") 6
      simpa [p] using this
    -- Conclude.
    calc
      FiniteDependence.MIS.Model.prob μ (cylStr (a := (0 : ℤ)) "1001001") +
          FiniteDependence.MIS.Model.prob μ (cylStr (a := (0 : ℤ)) "1010101")
          = FiniteDependence.MIS.Model.prob μ (cylStr (a := (0 : ℤ)) "1" ∩ cylStr (a := (6 : ℤ)) "1") := by
              simpa [hsum] using hsum.symm
      _ = p * p := by simpa [p, hs6p] using hind
      _ = p ^ 2 := by ring

  have hend00 :
      FiniteDependence.MIS.Model.prob μ (cylStr (a := (0 : ℤ)) "0010010") +
        FiniteDependence.MIS.Model.prob μ (cylStr (a := (0 : ℤ)) "0010100") +
          FiniteDependence.MIS.Model.prob μ (cylStr (a := (0 : ℤ)) "0100100") +
            FiniteDependence.MIS.Model.prob μ (cylStr (a := (0 : ℤ)) "0101010") =
              (1 - p) ^ 2 := by
    -- Same proof pattern as `hend11`.
    have hd :
        PairwiseDisjoint (↑good00 : Set String) (fun w => cylStr (a := (0 : ℤ)) w) := by
      intro w hw u hu hwu
      have hw0 : w ∈ allowedWordsFinset 7 := Finset.mem_of_mem_filter w hw
      have hu0 : u ∈ allowedWordsFinset 7 := Finset.mem_of_mem_filter u hu
      exact pairwiseDisjoint_cylStr_allowedWords (a := (0 : ℤ)) (L := 7) hw0 hu0 hwu
    have hm : ∀ w ∈ good00, MeasurableSet (cylStr (a := (0 : ℤ)) w) := by
      intro w _hw
      simpa using measurableSet_cylStr (a := (0 : ℤ)) (s := w)
    have hprobUnion :
        FiniteDependence.MIS.Model.prob μ (⋃ w ∈ good00, cylStr (a := (0 : ℤ)) w) =
          ∑ w ∈ good00, FiniteDependence.MIS.Model.prob μ (cylStr (a := (0 : ℤ)) w) :=
      prob_biUnion_finset (μ := μ) (s := good00) (f := fun w => cylStr (a := (0 : ℤ)) w) hd hm
    have hsum :
        FiniteDependence.MIS.Model.prob μ (cylStr (a := (0 : ℤ)) "0" ∩ cylStr (a := (6 : ℤ)) "0") =
          FiniteDependence.MIS.Model.prob μ (cylStr (a := (0 : ℤ)) "0010010") +
            FiniteDependence.MIS.Model.prob μ (cylStr (a := (0 : ℤ)) "0010100") +
              FiniteDependence.MIS.Model.prob μ (cylStr (a := (0 : ℤ)) "0100100") +
                FiniteDependence.MIS.Model.prob μ (cylStr (a := (0 : ℤ)) "0101010") := by
      have :
          FiniteDependence.MIS.Model.prob μ (cylStr (a := (0 : ℤ)) "0" ∩ cylStr (a := (6 : ℤ)) "0") =
            ∑ w ∈ good00, FiniteDependence.MIS.Model.prob μ (cylStr (a := (0 : ℤ)) w) := by
        calc
          FiniteDependence.MIS.Model.prob μ (cylStr (a := (0 : ℤ)) "0" ∩ cylStr (a := (6 : ℤ)) "0") =
              FiniteDependence.MIS.Model.prob μ (⋃ w ∈ good00, cylStr (a := (0 : ℤ)) w) := by
                simpa [cylStr_endpoints00_eq_union]
          _ = ∑ w ∈ good00, FiniteDependence.MIS.Model.prob μ (cylStr (a := (0 : ℤ)) w) := hprobUnion
      simpa [good00_eq, add_assoc, add_left_comm, add_comm] using this
    -- Independence.
    have hsep :
        ∀ i : Fin 1, ∀ j : Fin 1,
          Int.natAbs ((0 + Int.ofNat i.1) - (6 + Int.ofNat j.1)) > 5 := by
      intro i j; fin_cases i <;> fin_cases j <;> simp
    have hind :
        FiniteDependence.MIS.Model.prob μ (cylStr (a := (0 : ℤ)) "0" ∩ cylStr (a := (6 : ℤ)) "0") =
          FiniteDependence.MIS.Model.prob μ (cylStr (a := (0 : ℤ)) "0") *
            FiniteDependence.MIS.Model.prob μ (cylStr (a := (6 : ℤ)) "0") := by
      simpa [cylStr] using
        (FiniteDependence.MIS.Model.KDependent.prob_inter_cyl_eq_mul (μ := μ) (k := 5)
          (m := 1) (n := 1) (a := (0 : ℤ)) (b := (6 : ℤ)) hdep hsep
          (K5Bridge.wordOfString "0") (K5Bridge.wordOfString "0"))
    have hs60 :
        FiniteDependence.MIS.Model.prob μ (cylStr (a := (6 : ℤ)) "0") =
          FiniteDependence.MIS.Model.prob μ (cylStr (a := (0 : ℤ)) "0") := by
      have := prob_cylStr_add_nat (μ := μ) hstat (a := (0 : ℤ)) (s := "0") 6
      simpa using this
    have hb0 : FiniteDependence.MIS.Model.prob μ (cylStr (a := (0 : ℤ)) "0") = 1 - p := by
      simpa [p] using (prob_cylStr0_0_eq_one_sub_prob1 (μ := μ))
    calc
      FiniteDependence.MIS.Model.prob μ (cylStr (a := (0 : ℤ)) "0010010") +
          FiniteDependence.MIS.Model.prob μ (cylStr (a := (0 : ℤ)) "0010100") +
            FiniteDependence.MIS.Model.prob μ (cylStr (a := (0 : ℤ)) "0100100") +
              FiniteDependence.MIS.Model.prob μ (cylStr (a := (0 : ℤ)) "0101010")
          = FiniteDependence.MIS.Model.prob μ (cylStr (a := (0 : ℤ)) "0" ∩ cylStr (a := (6 : ℤ)) "0") := by
              simpa [hsum, add_assoc, add_left_comm, add_comm] using hsum.symm
      _ = (1 - p) * (1 - p) := by simpa [hb0, hs60] using hind
      _ = (1 - p) ^ 2 := by ring

  have hend01 :
      FiniteDependence.MIS.Model.prob μ (cylStr (a := (0 : ℤ)) "0010101") +
        FiniteDependence.MIS.Model.prob μ (cylStr (a := (0 : ℤ)) "0100101") +
          FiniteDependence.MIS.Model.prob μ (cylStr (a := (0 : ℤ)) "0101001") =
            (1 - p) * p := by
    have hd :
        PairwiseDisjoint (↑good01 : Set String) (fun w => cylStr (a := (0 : ℤ)) w) := by
      intro w hw u hu hwu
      have hw0 : w ∈ allowedWordsFinset 7 := Finset.mem_of_mem_filter w hw
      have hu0 : u ∈ allowedWordsFinset 7 := Finset.mem_of_mem_filter u hu
      exact pairwiseDisjoint_cylStr_allowedWords (a := (0 : ℤ)) (L := 7) hw0 hu0 hwu
    have hm : ∀ w ∈ good01, MeasurableSet (cylStr (a := (0 : ℤ)) w) := by
      intro w _hw
      simpa using measurableSet_cylStr (a := (0 : ℤ)) (s := w)
    have hprobUnion :
        FiniteDependence.MIS.Model.prob μ (⋃ w ∈ good01, cylStr (a := (0 : ℤ)) w) =
          ∑ w ∈ good01, FiniteDependence.MIS.Model.prob μ (cylStr (a := (0 : ℤ)) w) :=
      prob_biUnion_finset (μ := μ) (s := good01) (f := fun w => cylStr (a := (0 : ℤ)) w) hd hm
    have hsum :
        FiniteDependence.MIS.Model.prob μ (cylStr (a := (0 : ℤ)) "0" ∩ cylStr (a := (6 : ℤ)) "1") =
          FiniteDependence.MIS.Model.prob μ (cylStr (a := (0 : ℤ)) "0010101") +
            FiniteDependence.MIS.Model.prob μ (cylStr (a := (0 : ℤ)) "0100101") +
              FiniteDependence.MIS.Model.prob μ (cylStr (a := (0 : ℤ)) "0101001") := by
      have :
          FiniteDependence.MIS.Model.prob μ (cylStr (a := (0 : ℤ)) "0" ∩ cylStr (a := (6 : ℤ)) "1") =
            ∑ w ∈ good01, FiniteDependence.MIS.Model.prob μ (cylStr (a := (0 : ℤ)) w) := by
        calc
          FiniteDependence.MIS.Model.prob μ (cylStr (a := (0 : ℤ)) "0" ∩ cylStr (a := (6 : ℤ)) "1") =
              FiniteDependence.MIS.Model.prob μ (⋃ w ∈ good01, cylStr (a := (0 : ℤ)) w) := by
                simpa [cylStr_endpoints01_eq_union]
          _ = ∑ w ∈ good01, FiniteDependence.MIS.Model.prob μ (cylStr (a := (0 : ℤ)) w) := hprobUnion
      simpa [good01_eq, add_assoc, add_left_comm, add_comm] using this

    have hsep :
        ∀ i : Fin 1, ∀ j : Fin 1,
          Int.natAbs ((0 + Int.ofNat i.1) - (6 + Int.ofNat j.1)) > 5 := by
      intro i j; fin_cases i <;> fin_cases j <;> simp
    have hind :
        FiniteDependence.MIS.Model.prob μ (cylStr (a := (0 : ℤ)) "0" ∩ cylStr (a := (6 : ℤ)) "1") =
          FiniteDependence.MIS.Model.prob μ (cylStr (a := (0 : ℤ)) "0") *
            FiniteDependence.MIS.Model.prob μ (cylStr (a := (6 : ℤ)) "1") := by
      simpa [cylStr] using
        (FiniteDependence.MIS.Model.KDependent.prob_inter_cyl_eq_mul (μ := μ) (k := 5)
          (m := 1) (n := 1) (a := (0 : ℤ)) (b := (6 : ℤ)) hdep hsep
          (K5Bridge.wordOfString "0") (K5Bridge.wordOfString "1"))
    have hs61 :
        FiniteDependence.MIS.Model.prob μ (cylStr (a := (6 : ℤ)) "1") = p := by
      have := prob_cylStr_add_nat (μ := μ) hstat (a := (0 : ℤ)) (s := "1") 6
      simpa [p] using this
    have hb0 : FiniteDependence.MIS.Model.prob μ (cylStr (a := (0 : ℤ)) "0") = 1 - p := by
      simpa [p] using (prob_cylStr0_0_eq_one_sub_prob1 (μ := μ))
    calc
      FiniteDependence.MIS.Model.prob μ (cylStr (a := (0 : ℤ)) "0010101") +
          FiniteDependence.MIS.Model.prob μ (cylStr (a := (0 : ℤ)) "0100101") +
            FiniteDependence.MIS.Model.prob μ (cylStr (a := (0 : ℤ)) "0101001")
          = FiniteDependence.MIS.Model.prob μ (cylStr (a := (0 : ℤ)) "0" ∩ cylStr (a := (6 : ℤ)) "1") := by
              simpa [hsum, add_assoc, add_left_comm, add_comm] using hsum.symm
      _ = (1 - p) * p := by simpa [hb0, hs61] using hind

  -- Solve for the three key unknowns:
  --   a := P(0010010) = P(0100100) = P(1001001),
  --   b := P(0010100),
  --   c := P(0010101) (= P(1010100)).
  set a : ℝ := FiniteDependence.MIS.Model.prob μ (cylStr (a := 0) "0010010")
  set b : ℝ := FiniteDependence.MIS.Model.prob μ (cylStr (a := 0) "0010100")
  set c : ℝ := FiniteDependence.MIS.Model.prob μ (cylStr (a := 0) "0010101")

  have ha_eq : a = p ^ 2 - t := by
    have : a + t = p ^ 2 := by
      -- rewrite `hend11` and use the stationarity equalities
      simpa [a, t, p, h001001] using hend11
    linarith

  have hb1 : FiniteDependence.MIS.Model.prob μ (cylStr (a := (0 : ℤ)) "0101010") = c + t := by
    linarith [h0101010_eq_0010101_add_t]

  have hb_eq : b + c = -p ^ 2 - 2 * p + t + 1 := by
    -- From `b+c = P(1001010)` and stationarity to `P(0100101)`.
    have : b + c = FiniteDependence.MIS.Model.prob μ (cylStr (a := 0) "1001010") := by
      simpa [b, c] using h001010
    have : b + c = FiniteDependence.MIS.Model.prob μ (cylStr (a := 0) "0100101") := by
      linarith [this, h100101]
    -- Use `hend00` to solve for this common value.
    have h00 :
        a + b + a + (c + t) = (1 - p) ^ 2 := by
      -- Expand `hend00` and rewrite `P(0100100)=a`, `P(0101010)=c+t`.
      have h0100100' : FiniteDependence.MIS.Model.prob μ (cylStr (a := 0) "0100100") = a := by
        simpa [a] using h0010010_eq_0100100.symm
      have h0101010' : FiniteDependence.MIS.Model.prob μ (cylStr (a := 0) "0101010") = c + t := by
        simpa [c, t] using h0101010_eq_0010101_add_t
      simpa [a, b, h0100100', h0101010'] using hend00
    -- Rearranged equation `b + c = 1 - 2p - p^2 + t`.
    have : b + c = 1 - 2 * p - p ^ 2 + t := by
      -- Substitute `a = p^2 - t`.
      linarith [h00, ha_eq]
    -- Put into the exact normal form used later.
    nlinarith [this]

  have hbc_eq : 2 * b + 3 * c = p - p ^ 2 := by
    -- Use `hend01` and the stationarity equalities:
    -- `P(0100101)=P(0101001)=b+c`.
    have h1 : FiniteDependence.MIS.Model.prob μ (cylStr (a := 0) "0100101") = b + c := by
      simpa [b, c] using h0100101_eq_u
    have h2 : FiniteDependence.MIS.Model.prob μ (cylStr (a := 0) "0101001") = b + c := by
      simpa [b, c] using h0101001_eq_u
    have hsum : c + (b + c) + (b + c) = (1 - p) * p := by
      simpa [c, h1, h2] using hend01
    calc
      2 * b + 3 * c = c + (b + c) + (b + c) := by ring
      _ = (1 - p) * p := hsum
      _ = p - p ^ 2 := by ring

  have hc_eq : c = p ^ 2 + 5 * p - 2 * t - 2 := by
    -- Subtract `2*(b+c = 1 - 2p - p^2 + t)` from `2b + 3c = p - p^2`.
    have hbc : b + c = 1 - 2 * p - p ^ 2 + t := by
      calc
        b + c = -p ^ 2 - 2 * p + t + 1 := hb_eq
        _ = 1 - 2 * p - p ^ 2 + t := by ring
    have hc : c = (p - p ^ 2) - 2 * (1 - 2 * p - p ^ 2 + t) := by
      linarith [hbc_eq, hbc]
    calc
      c = (p - p ^ 2) - 2 * (1 - 2 * p - p ^ 2 + t) := hc
      _ = p ^ 2 + 5 * p - 2 * t - 2 := by ring

  have hb0_eq : b = (-2) * p ^ 2 + (-7) * p + 3 * t + 3 := by
    have hbc : b = (b + c) - c := by ring
    have hbc' : b + c = 1 - 2 * p - p ^ 2 + t := by
      calc
        b + c = -p ^ 2 - 2 * p + t + 1 := hb_eq
        _ = 1 - 2 * p - p ^ 2 + t := by ring
    calc
      b = (b + c) - c := hbc
      _ = (1 - 2 * p - p ^ 2 + t) - (p ^ 2 + 5 * p - 2 * t - 2) := by
          rw [hbc', hc_eq]
      _ = (-2) * p ^ 2 + (-7) * p + 3 * t + 3 := by linarith

  have h0100101_eq : FiniteDependence.MIS.Model.prob μ (cylStr (a := 0) "0100101") =
      (-1) * p ^ 2 + (-2) * p + t + 1 := by
    -- `P(0100101) = b + c`.
    have hprob : FiniteDependence.MIS.Model.prob μ (cylStr (a := 0) "0100101") = b + c := by
      simpa [b, c] using h0100101_eq_u
    calc
      FiniteDependence.MIS.Model.prob μ (cylStr (a := 0) "0100101") = b + c := hprob
      _ = -p ^ 2 - 2 * p + t + 1 := hb_eq
      _ = (-1) * p ^ 2 + (-2) * p + t + 1 := by ring

  have h0101001_eq : FiniteDependence.MIS.Model.prob μ (cylStr (a := 0) "0101001") =
      (-1) * p ^ 2 + (-2) * p + t + 1 := by
    -- `P(0101001) = P(0100101)`.
    calc
      FiniteDependence.MIS.Model.prob μ (cylStr (a := 0) "0101001") =
          FiniteDependence.MIS.Model.prob μ (cylStr (a := 0) "0100101") := h0101001_eq_0100101
      _ = (-1) * p ^ 2 + (-2) * p + t + 1 := h0100101_eq

  have h1001010_eq : FiniteDependence.MIS.Model.prob μ (cylStr (a := 0) "1001010") =
      (-1) * p ^ 2 + (-2) * p + t + 1 := by
    -- `P(1001010) = P(0100101)`.
    calc
      FiniteDependence.MIS.Model.prob μ (cylStr (a := 0) "1001010") =
          FiniteDependence.MIS.Model.prob μ (cylStr (a := 0) "0100101") := h100101
      _ = (-1) * p ^ 2 + (-2) * p + t + 1 := h0100101_eq

  have h1010010_eq : FiniteDependence.MIS.Model.prob μ (cylStr (a := 0) "1010010") =
      (-1) * p ^ 2 + (-2) * p + t + 1 := by
    -- `P(1010010) = P(0100101)`.
    calc
      FiniteDependence.MIS.Model.prob μ (cylStr (a := 0) "1010010") =
          FiniteDependence.MIS.Model.prob μ (cylStr (a := 0) "0100101") := h1010010_eq_0100101
      _ = (-1) * p ^ 2 + (-2) * p + t + 1 := h0100101_eq

  have h1010100_eq : FiniteDependence.MIS.Model.prob μ (cylStr (a := 0) "1010100") =
      p ^ 2 + 5 * p - 2 * t - 2 := by
    -- `P(1010100) = P(0010101) = c`.
    calc
      FiniteDependence.MIS.Model.prob μ (cylStr (a := 0) "1010100") =
          FiniteDependence.MIS.Model.prob μ (cylStr (a := 0) "0010101") := h1010100_eq_0010101
      _ = c := by simpa [c]
      _ = p ^ 2 + 5 * p - 2 * t - 2 := hc_eq

  have h0101010_eq : FiniteDependence.MIS.Model.prob μ (cylStr (a := 0) "0101010") =
      p ^ 2 + 5 * p - t - 2 := by
    -- `P(0101010) = c + t`.
    calc
      FiniteDependence.MIS.Model.prob μ (cylStr (a := (0 : ℤ)) "0101010") = c + t := by
        simpa [c] using h0101010_eq_0010101_add_t
      _ = (p ^ 2 + 5 * p - 2 * t - 2) + t := by simpa [hc_eq]
      _ = p ^ 2 + 5 * p - t - 2 := by ring

  -- Collect the final list in the requested order.
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · -- 0010010
    calc
      FiniteDependence.MIS.Model.prob μ (cylStr (a := 0) "0010010") = a := by simpa [a]
      _ = p ^ 2 - t := ha_eq
  · -- 0010100
    calc
      FiniteDependence.MIS.Model.prob μ (cylStr (a := 0) "0010100") = b := by simpa [b]
      _ = (-2) * p ^ 2 + (-7) * p + 3 * t + 3 := hb0_eq
  · -- 0010101
    calc
      FiniteDependence.MIS.Model.prob μ (cylStr (a := 0) "0010101") = c := by simpa [c]
      _ = p ^ 2 + 5 * p - 2 * t - 2 := hc_eq
  · -- 0100100
    calc
      FiniteDependence.MIS.Model.prob μ (cylStr (a := 0) "0100100") =
          FiniteDependence.MIS.Model.prob μ (cylStr (a := 0) "0010010") := by
            simpa using h0010010_eq_0100100.symm
      _ = p ^ 2 - t := by
            calc
              FiniteDependence.MIS.Model.prob μ (cylStr (a := 0) "0010010") = a := by simpa [a]
              _ = p ^ 2 - t := ha_eq
  · -- 0100101
    simpa using h0100101_eq
  · -- 0101001
    simpa using h0101001_eq
  · -- 0101010
    simpa using h0101010_eq
  · -- 1001001
    calc
      FiniteDependence.MIS.Model.prob μ (cylStr (a := 0) "1001001") =
          FiniteDependence.MIS.Model.prob μ (cylStr (a := 0) "0010010") := by
            simpa using h001001.symm
      _ = p ^ 2 - t := by
            calc
              FiniteDependence.MIS.Model.prob μ (cylStr (a := 0) "0010010") = a := by simpa [a]
              _ = p ^ 2 - t := ha_eq
  · -- 1001010
    simpa using h1001010_eq
  · -- 1010010
    simpa using h1010010_eq
  · -- 1010100
    simpa using h1010100_eq
  · -- 1010101
    rfl

end

end Model

end K5Bridge

end FiniteDependence.MIS
