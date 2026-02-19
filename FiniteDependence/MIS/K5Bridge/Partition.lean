import FiniteDependence.MIS.K5Bridge.AllowedWords01

namespace FiniteDependence.MIS

/-!
Finite partition facts for the cylinder sets `State.cylStr` indexed by `K5Data.allowedWords`.

For `L > 0`, the length-`L` cylinders at a fixed position form a disjoint cover of `State`.
This is the basic set-theoretic backbone for turning word-indexed arrays into probabilities.
-/

namespace K5Bridge

open K5Data

open MeasureTheory Set

/-- All words in an array have length `L`. -/
def AllLen (words : Array String) (L : Nat) : Prop :=
  ∀ s ∈ words.toList, s.length = L

private lemma length_of_push (w : String) (c : Char) : (w.push c).length = w.length + 1 := by
  simp [String.length_push]

private lemma length_of_mem_extensions {w s : String} (hs : s ∈ K5Data.extensions w) :
    s.length = w.length + 1 := by
  classical
  -- Case-split on the last 1–2 characters of `w` (as `reverse` head(s)).
  cases hrev : w.toList.reverse with
  | nil =>
      have hs' : s = w.push '0' ∨ s = w.push '1' := by
        simpa [K5Data.extensions, hrev] using hs
      cases hs' with
      | inl h => simpa [h, length_of_push] using (rfl : (w.push '0').length = (w.push '0').length)
      | inr h => simpa [h, length_of_push] using (rfl : (w.push '1').length = (w.push '1').length)
  | cons c tail =>
      -- Decide whether we are in the `'1' :: _` branch.
      by_cases hc1 : c = '1'
      · subst hc1
        have hs0 : s = w.push '0' := by
          simpa [K5Data.extensions, hrev] using hs
        simpa [hs0, length_of_push]
      · -- Otherwise, decide whether we are in the `'0' :: '0' :: _` branch.
        cases tail with
        | nil =>
            have hs' : s = w.push '0' ∨ s = w.push '1' := by
              simpa [K5Data.extensions, hrev, hc1] using hs
            cases hs' with
            | inl h => simpa [h, length_of_push]
            | inr h => simpa [h, length_of_push]
        | cons c2 tail2 =>
            by_cases hc0 : c = '0'
            · subst hc0
              by_cases hc20 : c2 = '0'
              · subst hc20
                have hs1 : s = w.push '1' := by
                  simpa [K5Data.extensions, hrev, hc1] using hs
                simpa [hs1, length_of_push]
              · have hs' : s = w.push '0' ∨ s = w.push '1' := by
                  simpa [K5Data.extensions, hrev, hc1, hc20] using hs
                cases hs' with
                | inl h => simpa [h, length_of_push]
                | inr h => simpa [h, length_of_push]
            · have hs' : s = w.push '0' ∨ s = w.push '1' := by
                -- Here we are in the default branch.
                simpa [K5Data.extensions, hrev, hc1, hc0] using hs
              cases hs' with
              | inl h => simpa [h, length_of_push]
              | inr h => simpa [h, length_of_push]

lemma allLen_base : AllLen (#["0", "1"] : Array String) 1 := by
  intro s hs
  have : s = "0" ∨ s = "1" := by
    simpa using hs
  cases this with
  | inl h =>
      subst h
      native_decide
  | inr h =>
      subst h
      native_decide

lemma allLen_extendWords {words : Array String} {L : Nat} (hwords : AllLen words L) :
    AllLen (K5Data.extendWords words) (L + 1) := by
  classical
  intro s hs
  have hs' : s ∈ words.toList.flatMap K5Data.extensions := by
    simpa [K5Data.extendWords, List.toList_toArray] using hs
  rcases List.mem_flatMap.mp hs' with ⟨w, hw_mem, hs_ext⟩
  have hw_len : w.length = L := hwords w hw_mem
  have hs_len : s.length = w.length + 1 := length_of_mem_extensions (w := w) (s := s) hs_ext
  simpa [hw_len, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hs_len

lemma allLen_iterate_extendWords {words : Array String} {L : Nat} (hwords : AllLen words L) (n : Nat) :
    AllLen (Nat.iterate K5Data.extendWords n words) (L + n) := by
  induction n generalizing words L with
  | zero =>
      simpa [Nat.iterate]
  | succ n ih =>
      -- Unfold one `extendWords` step and use the induction hypothesis.
      have hwords' : AllLen (K5Data.extendWords words) (L + 1) :=
        allLen_extendWords (words := words) (L := L) hwords
      have := ih (words := K5Data.extendWords words) (L := L + 1) hwords'
      -- `Nat.iterate` applies the function first in the successor case.
      simpa [Nat.iterate, Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using this

lemma length_of_mem_allowedWords {L : Nat} {s : String} (hs : s ∈ K5Data.allowedWords L) :
    s.length = L := by
  classical
  by_cases hL : L = 0
  · subst hL
    simpa [K5Data.allowedWords] using hs
  · -- Reduce to the successor case.
    cases L with
    | zero =>
        cases (hL rfl)
    | succ n =>
        -- `allowedWords (n+1) = iterate extendWords n base`.
        have hAll :
            AllLen (Nat.iterate K5Data.extendWords n (#["0", "1"] : Array String)) (1 + n) :=
          allLen_iterate_extendWords (words := (#["0", "1"] : Array String)) (L := 1) allLen_base (n := n)
        have hs' : s ∈ (Nat.iterate K5Data.extendWords n (#["0", "1"] : Array String)).toList := by
          simpa [K5Data.allowedWords] using hs
        have : s.length = 1 + n := hAll s hs'
        simpa [Nat.succ_eq_add_one, Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using this

namespace Model

open FiniteDependence.MIS.Model

noncomputable section

/-- A finset view of `allowedWords L` (deduplicated). -/
def allowedWordsFinset (L : Nat) : Finset String :=
  (K5Data.allowedWords L).toList.toFinset

lemma mem_allowedWordsFinset_iff {L : Nat} {s : String} :
    s ∈ allowedWordsFinset L ↔ s ∈ K5Data.allowedWords L := by
  classical
  -- `allowedWordsFinset` is `toFinset` of the underlying list.
  simpa [allowedWordsFinset, List.mem_toFinset]

lemma measurableSet_cylStr (a : ℤ) (s : String) : MeasurableSet (cylStr (a := a) s) := by
  simpa [cylStr] using FiniteDependence.MIS.Model.measurableSet_cyl (a := a) (w := K5Bridge.wordOfString s)

lemma cylStr_disjoint_of_ne_len (a : ℤ) {L : Nat} {s t : String}
    (hs01 : Is01String s) (ht01 : Is01String t) (hsL : s.length = L) (htL : t.length = L)
    (hst : s ≠ t) :
    Disjoint (cylStr (a := a) s) (cylStr (a := a) t) := by
  classical
  refine disjoint_left.2 ?_
  intro ω hs ht
  have hs' : blockString a L ω = s := by
    -- rewrite the length in `mem_cylStr_iff_blockString_eq`
    have := (mem_cylStr_iff_blockString_eq (a := a) s ω hs01).1 hs
    simpa [hsL] using this
  have ht' : blockString a L ω = t := by
    have := (mem_cylStr_iff_blockString_eq (a := a) t ω ht01).1 ht
    simpa [htL] using this
  exact hst (by simpa [hs'] using ht')

lemma pairwiseDisjoint_cylStr_allowedWords (a : ℤ) (L : Nat) :
    PairwiseDisjoint (↑(allowedWordsFinset L) : Set String) (fun s => cylStr (a := a) s) := by
  classical
  intro s hs t ht hst
  have hs_allowed : s ∈ K5Data.allowedWords L := (mem_allowedWordsFinset_iff (L := L) (s := s)).1 hs
  have ht_allowed : t ∈ K5Data.allowedWords L := (mem_allowedWordsFinset_iff (L := L) (s := t)).1 ht
  have hs01 : Is01String s := Is01String.of_mem_allowedWords (L := L) (s := s) hs_allowed
  have ht01 : Is01String t := Is01String.of_mem_allowedWords (L := L) (s := t) ht_allowed
  have hsL : s.length = L := length_of_mem_allowedWords (L := L) (s := s) hs_allowed
  have htL : t.length = L := length_of_mem_allowedWords (L := L) (s := t) ht_allowed
  exact cylStr_disjoint_of_ne_len (a := a) (L := L) (s := s) (t := t) hs01 ht01 hsL htL hst

lemma iUnion_cylStr_allowedWords (a : ℤ) {L : Nat} (hL : 0 < L) :
    (⋃ s ∈ allowedWordsFinset L, cylStr (a := a) s) = (univ : Set FiniteDependence.MIS.State) := by
  classical
  ext ω
  constructor
  · intro hω
    -- Trivial: union is subset of `univ`.
    exact mem_univ ω
  · intro _
    -- Choose `s = blockString a L ω`.
    cases L with
    | zero =>
        cases (Nat.lt_asymm hL hL)
    | succ n =>
        let s : String := blockString a (n + 1) ω
        have hs_allowed : s ∈ K5Data.allowedWords (n + 1) := by
          simpa [s] using K5Bridge.Model.blockString_mem_allowedWords (ω := ω) (a := a) (n := n)
        have hs_fin : s ∈ allowedWordsFinset (n + 1) :=
          (mem_allowedWordsFinset_iff (L := n + 1) (s := s)).2 hs_allowed
        have hs01 : Is01String s := Is01String.of_mem_allowedWords (L := n + 1) (s := s) hs_allowed
        have hmem : ω ∈ cylStr (a := a) s := by
          -- membership is exactly `blockString = s`
          have hsLen : s.length = n + 1 := by
            simpa [s] using (K5Bridge.Model.blockString_length (a := a) (n := n + 1) (ω := ω))
          have : blockString a s.length ω = s := by
            simpa [s, hsLen]
          exact (mem_cylStr_iff_blockString_eq (a := a) s ω hs01).2 this
        -- Now finish via the finset union membership lemma.
        refine mem_iUnion.2 ?_
        refine ⟨s, mem_iUnion.2 ?_⟩
        exact ⟨hs_fin, hmem⟩

end

end Model

end K5Bridge

end FiniteDependence.MIS
