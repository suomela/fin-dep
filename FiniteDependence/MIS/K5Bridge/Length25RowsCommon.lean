import FiniteDependence.MIS.K5Bridge.StepLemmas

namespace FiniteDependence.MIS

namespace K5Bridge

open MeasureTheory Set
open scoped ProbabilityTheory

namespace Model

open FiniteDependence.MIS.Model
open K5Data

noncomputable section

set_option maxRecDepth 1000000
set_option maxHeartbeats 20000000

lemma mem_allowedWords_of_finset {L : Nat} {s : String} (hs : s ∈ allowedWordsFinset L) :
    s ∈ K5Data.allowedWords L :=
  (mem_allowedWordsFinset_iff (L := L) (s := s)).1 hs

lemma true_prev_false (ω : FiniteDependence.MIS.State) {i : ℤ} (hi : ω.1 i = true) :
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

lemma natAbs_sub_eq_sub_of_le {a b : Nat} (hle : a ≤ b) :
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

lemma bit_eq_of_mem_cylStr {a : ℤ} {s : String} {ω : FiniteDependence.MIS.State}
    (h : ω ∈ cylStr (a := a) s) (i : Fin s.length) :
    ω.1 (a + Int.ofNat i.1) = K5Bridge.wordOfString s i := by
  have hcyl : ω ∈ FiniteDependence.MIS.Model.cyl a (K5Bridge.wordOfString s) := by
    simpa [cylStr] using h
  simpa using (FiniteDependence.MIS.Model.bit_eq_of_mem_cyl (h := hcyl) (i := i))

lemma is01_of_toList_eq {s : String} {cs : List Char} (h : s.toList = cs)
    (h01 : ∀ c ∈ cs, c = '0' ∨ c = '1') : Is01String s := by
  intro c hc
  rw [h] at hc
  exact h01 c hc

lemma is01_append {s t : String} (hs : Is01String s) (ht : Is01String t) :
    Is01String (s ++ t) := by
  intro c hc
  rw [String.toList_append, List.mem_append] at hc
  rcases hc with hc | hc
  · exact hs c hc
  · exact ht c hc

def wA : String := "0010010010101010010010100"
def wB : String := "0101010010101010010010100"
def wC : String := "0010010100101010010010100"

def suf19 : String := "0010101010010010100"
def suf15 : String := "101010010010100"
def mid10 : String := "0010010100"
def suf24 : String := "101010010101010010010100"

lemma wA_len : wA.length = 25 := by decide
lemma wB_len : wB.length = 25 := by decide
lemma wC_len : wC.length = 25 := by decide

lemma suf19_len : suf19.length = 19 := by decide
lemma suf15_len : suf15.length = 15 := by decide
lemma mid10_len : mid10.length = 10 := by decide
lemma suf24_len : suf24.length = 24 := by decide

lemma wA_eq_pre6 : wA = ("001001" : String) ++ suf19 := by decide
lemma wB_eq_pre6 : wB = ("010101" : String) ++ suf19 := by decide

lemma wA_eq_pre5 : wA = ("00100" : String) ++ ("10010" : String) ++ suf15 := by decide
lemma wC_eq_pre5 : wC = ("00100" : String) ++ ("10100" : String) ++ suf15 := by decide

lemma wC_eq_mid10 : wC = mid10 ++ ("10101" : String) ++ mid10 := by decide
lemma wB_eq_suf24 : wB = ("0" : String) ++ suf24 := by decide

lemma blockString_add (ω : FiniteDependence.MIS.State) (a : ℤ) (m n : Nat) :
    blockString a (m + n) ω = (blockString a m ω) ++ (blockString (a + m) n ω) := by
  apply String.ext
  simpa [String.toList_append] using
    (toList_blockString_add (ω := ω) (a := a) (m := m) (n := n))

end

end Model

end K5Bridge

end FiniteDependence.MIS
