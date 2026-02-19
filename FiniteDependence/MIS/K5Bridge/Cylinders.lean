import FiniteDependence.MIS.K5Bridge.AllowedWords
import FiniteDependence.MIS.K5Bridge.Dist
import Mathlib.Data.List.OfFn

namespace FiniteDependence.MIS

/-!
Basic cylinder lemmas for the k=5 bridge.

We use `K5Bridge.Model.blockString` to turn an `ω : State` block into a binary `String`.
This file relates that representation to the cylinder sets `State.cyl` used in the
probabilistic model.
-/

namespace K5Bridge

open K5Data

/-- A string is *binary* if every character is `'0'` or `'1'`. -/
def Is01String (s : String) : Prop :=
  ∀ c ∈ s.toList, c = '0' ∨ c = '1'

lemma Is01String.of_mem {s : String} (hs : Is01String s) (i : Fin s.length) :
    s.toList.get ⟨i.1, by simpa [String.length_toList] using i.2⟩ = '0' ∨
      s.toList.get ⟨i.1, by simpa [String.length_toList] using i.2⟩ = '1' := by
  have hmem :
      s.toList.get ⟨i.1, by simpa [String.length_toList] using i.2⟩ ∈ s.toList :=
    List.get_mem _ _
  simpa using hs _ hmem

namespace Model

open FiniteDependence.MIS.Model

noncomputable section

/-- Convert a Boolean bit to a `'0'`/`'1'` character. -/
def bitChar (b : Bool) : Char := if b then '1' else '0'

lemma decide_bitChar_eq (b : Bool) : decide (bitChar b = '1') = b := by
  cases b <;> rfl

lemma blockString_is01 (a : ℤ) (n : Nat) (ω : FiniteDependence.MIS.State) :
    Is01String (blockString a n ω) := by
  classical
  intro c hc
  -- Every character in `blockString` is produced by `bitChar`.
  -- We prove this by induction on `n`.
  induction n with
  | zero =>
      simpa [blockString] using hc
  | succ n ih =>
      -- `toList` of a `push` is an append.
      have : c ∈ (blockString a n ω).toList ∨ c = bitChar (ω.1 (a + Int.ofNat n)) := by
        simpa [blockString, String.toList_push, List.mem_append, List.mem_singleton] using hc
      rcases this with hc' | rfl
      · exact ih hc'
      · cases ω.1 (a + Int.ofNat n) <;> simp [bitChar]

lemma toList_blockString (a : ℤ) (n : Nat) (ω : FiniteDependence.MIS.State) :
    (blockString a n ω).toList =
      List.ofFn (fun i : Fin n => bitChar (ω.1 (a + Int.ofNat i.1))) := by
  induction n with
  | zero =>
      simp [blockString]
  | succ n ih =>
      -- Keep the RHS in `ofFn` form; we want the append-at-the-end expansion.
      simp only [blockString, String.toList_push]
      rw [List.ofFn_succ']
      simp [ih, List.concat_eq_append, Fin.last, bitChar]

lemma block_eq_wordOfString_blockString (a : ℤ) (n : Nat) (ω : FiniteDependence.MIS.State) :
    FiniteDependence.MIS.Model.block a n ω =
      (fun i : Fin n =>
        K5Bridge.wordOfString (blockString a n ω)
          ⟨i.1, by
            simpa [blockString_length (a := a) (n := n) (ω := ω)] using i.2
          ⟩) := by
  funext i
  -- Unfold `block` and `wordOfString` and use the explicit `toList` description.
  simp [FiniteDependence.MIS.Model.block, K5Bridge.wordOfString, toList_blockString,
    List.get_ofFn, decide_bitChar_eq]

lemma char_eq_bitChar_of_is01 {c : Char} {b : Bool} (hc01 : c = '0' ∨ c = '1')
    (hb : b = decide (c = '1')) : c = bitChar b := by
  cases hc01 with
  | inl hc0 =>
      subst hc0
      have : b = false := by simpa using hb
      subst this
      rfl
  | inr hc1 =>
      subst hc1
      have : b = true := by simpa using hb
      subst this
      rfl

lemma blockString_eq_of_block_eq_wordOfString {a : ℤ} {s : String}
    (hs01 : Is01String s) (ω : FiniteDependence.MIS.State)
    (h : FiniteDependence.MIS.Model.block a s.length ω = K5Bridge.wordOfString s) :
    blockString a s.length ω = s := by
  classical
  apply String.ext
  -- Compare the `toList`s pointwise.
  apply List.ext_getElem
  · simp [String.length_toList, blockString_length]
  · intro n hn1 hn2
    let i : Fin s.length := ⟨n, by simpa [String.length_toList] using hn2⟩
    have hw : ω.1 (a + Int.ofNat n) = K5Bridge.wordOfString s i := by
      simpa [i] using (FiniteDependence.MIS.Model.bit_eq_of_block_eq (h := h) (i := i))
    let c : Char := s.toList[n]
    have hc_mem : c ∈ s.toList := by
      simpa [c] using List.getElem_mem (l := s.toList) hn2
    have hc01 : c = '0' ∨ c = '1' := hs01 c hc_mem
    have hb : ω.1 (a + Int.ofNat n) = decide (c = '1') := by
      simpa [K5Bridge.wordOfString, c, i] using hw
    have hc : c = bitChar (ω.1 (a + Int.ofNat n)) :=
      char_eq_bitChar_of_is01 (c := c) (b := ω.1 (a + Int.ofNat n)) hc01 (by simpa [hb])
    have hL : (blockString a s.length ω).toList[n] = bitChar (ω.1 (a + Int.ofNat n)) := by
      simp [toList_blockString, List.getElem_ofFn]
    have hR : s.toList[n] = c := by rfl
    simpa [hL, hR, hc]

lemma mem_cylStr_iff_blockString_eq (a : ℤ) (s : String) (ω : FiniteDependence.MIS.State)
    (hs01 : Is01String s) :
    ω ∈ cylStr (a := a) s ↔ blockString a s.length ω = s := by
  constructor
  · intro hω
    -- Membership in `cyl` is exactly a `block` equality.
    have hblock :
        FiniteDependence.MIS.Model.block a s.length ω = K5Bridge.wordOfString s := by
      simpa [cylStr, FiniteDependence.MIS.Model.cyl] using hω
    exact blockString_eq_of_block_eq_wordOfString (a := a) (s := s) hs01 ω hblock
  · intro hs
    -- Use the canonical description of `block` for `blockString`, then rewrite by `hs`.
    have hblock :
        FiniteDependence.MIS.Model.block a s.length ω =
          (fun i : Fin s.length =>
            K5Bridge.wordOfString (blockString a s.length ω)
              ⟨i.1, by
                simpa [blockString_length (a := a) (n := s.length) (ω := ω)] using i.2
              ⟩) :=
      block_eq_wordOfString_blockString (a := a) (n := s.length) (ω := ω)
    have hblock' : FiniteDependence.MIS.Model.block a s.length ω = K5Bridge.wordOfString s := by
      -- Rewrite `blockString a s.length ω` to `s` in the RHS.
      -- `simp` unfolds `wordOfString` and rewrites the `toList`.
      funext i
      -- Reduce to the previously proved pointwise statement.
      have := FiniteDependence.MIS.Model.bit_eq_of_block_eq (h := hblock) (i := i)
      simpa [hs, K5Bridge.wordOfString] using this
    simpa [cylStr, FiniteDependence.MIS.Model.cyl, hblock']

end

end Model

end K5Bridge

end FiniteDependence.MIS
