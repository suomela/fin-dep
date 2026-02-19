import FiniteDependence.MIS.K5Bridge.Cylinders

namespace FiniteDependence.MIS

/-!
Small helper facts about `K5Data.allowedWords`.

In particular, every word in `allowedWords L` is a binary string (`'0'`/`'1'` only).
This is used when relating cylinder sets to `blockString` in `K5Bridge.Cylinders`.
-/

namespace K5Bridge

open K5Data

lemma Is01String.push {s : String} (hs : Is01String s) {c : Char} (hc : c = '0' ∨ c = '1') :
    Is01String (s.push c) := by
  intro d hd
  have hd' : d ∈ s.toList ∨ d = c := by
    simpa [String.toList_push, List.mem_append, List.mem_singleton] using hd
  cases hd' with
  | inl hd0 => exact hs d hd0
  | inr hd1 => simpa [hd1] using hc

lemma Is01String.of_mem_extensions {w s : String} (hw : Is01String w) (hs : s ∈ K5Data.extensions w) :
    Is01String s := by
  classical
  cases hrev : w.toList.reverse with
  | nil =>
      have hs' : s = w.push '0' ∨ s = w.push '1' := by
        simpa [K5Data.extensions, hrev] using hs
      cases hs' with
      | inl h =>
          subst h
          exact Is01String.push (s := w) hw (Or.inl rfl)
      | inr h =>
          subst h
          exact Is01String.push (s := w) hw (Or.inr rfl)
  | cons c tail =>
      have hc_mem_rev : c ∈ w.toList.reverse := by simp [hrev]
      have hc_mem : c ∈ w.toList := by simpa [List.mem_reverse] using hc_mem_rev
      have hc01 : c = '0' ∨ c = '1' := hw c hc_mem
      cases hc01 with
      | inr hc1 =>
          subst hc1
          have hs0 : s = w.push '0' := by
            simpa [K5Data.extensions, hrev] using hs
          subst hs0
          exact Is01String.push (s := w) hw (Or.inl rfl)
      | inl hc0 =>
          subst hc0
          cases tail with
          | nil =>
              have hs' : s = w.push '0' ∨ s = w.push '1' := by
                simpa [K5Data.extensions, hrev] using hs
              cases hs' with
              | inl h =>
                  subst h
                  exact Is01String.push (s := w) hw (Or.inl rfl)
              | inr h =>
                  subst h
                  exact Is01String.push (s := w) hw (Or.inr rfl)
          | cons c2 tail2 =>
              have hc2_mem_rev : c2 ∈ w.toList.reverse := by simp [hrev]
              have hc2_mem : c2 ∈ w.toList := by simpa [List.mem_reverse] using hc2_mem_rev
              have hc2_01 : c2 = '0' ∨ c2 = '1' := hw c2 hc2_mem
              cases hc2_01 with
              | inl hc20 =>
                  subst hc20
                  have hs1 : s = w.push '1' := by
                    simpa [K5Data.extensions, hrev] using hs
                  subst hs1
                  exact Is01String.push (s := w) hw (Or.inr rfl)
              | inr hc21 =>
                  subst hc21
                  have hs' : s = w.push '0' ∨ s = w.push '1' := by
                    simpa [K5Data.extensions, hrev] using hs
                  cases hs' with
                  | inl h =>
                      subst h
                      exact Is01String.push (s := w) hw (Or.inl rfl)
                  | inr h =>
                      subst h
                      exact Is01String.push (s := w) hw (Or.inr rfl)

/-- All words in an array are binary strings. -/
def All01 (words : Array String) : Prop :=
  ∀ s ∈ words.toList, Is01String s

lemma all01_base : All01 (#["0", "1"] : Array String) := by
  intro s hs
  have : s = "0" ∨ s = "1" := by
    simpa using hs
  cases this with
  | inl h =>
      subst h
      intro c hc
      have h0 : ("0".toList) = ['0'] := by
        native_decide
      have hc0 : c = '0' := by
        have : c ∈ ['0'] := by simpa [h0] using hc
        simpa using this
      exact Or.inl hc0
  | inr h =>
      subst h
      intro c hc
      have h1 : ("1".toList) = ['1'] := by
        native_decide
      have hc1 : c = '1' := by
        have : c ∈ ['1'] := by simpa [h1] using hc
        simpa using this
      exact Or.inr hc1

lemma all01_extendWords {words : Array String} (hwords : All01 words) : All01 (K5Data.extendWords words) := by
  classical
  intro s hs
  have hs' : s ∈ words.toList.flatMap K5Data.extensions := by
    simpa [K5Data.extendWords, List.toList_toArray] using hs
  rcases List.mem_flatMap.mp hs' with ⟨w, hw_mem, hs_ext⟩
  exact Is01String.of_mem_extensions (w := w) (s := s) (hwords w hw_mem) hs_ext

lemma all01_iterate_extendWords {words : Array String} (hwords : All01 words) (n : Nat) :
    All01 (Nat.iterate K5Data.extendWords n words) := by
  induction n generalizing words with
  | zero =>
      simpa [Nat.iterate] using hwords
  | succ n ih =>
      have hwords' : All01 (K5Data.extendWords words) := all01_extendWords (words := words) hwords
      simpa [Nat.iterate] using ih (words := K5Data.extendWords words) hwords'

lemma Is01String.of_mem_allowedWords {L : Nat} {s : String} (hs : s ∈ K5Data.allowedWords L) :
    Is01String s := by
  classical
  by_cases hL : L = 0
  · subst hL
    simpa [K5Data.allowedWords] using hs
  · have hAll : All01 (Nat.iterate K5Data.extendWords (L - 1) (#["0", "1"] : Array String)) :=
      all01_iterate_extendWords (words := #["0", "1"]) all01_base (n := L - 1)
    have hs' : s ∈ (Nat.iterate K5Data.extendWords (L - 1) (#["0", "1"] : Array String)).toList := by
      simpa [K5Data.allowedWords, hL] using hs
    exact hAll s hs'

end K5Bridge

end FiniteDependence.MIS
