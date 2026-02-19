import FiniteDependence.MIS.K5Data.Defs

namespace FiniteDependence.MIS

/-!
No-duplicate facts about the `K5Data.allowedWords` enumeration.

These are used when turning array-based prefix sums (which fold over the
enumeration) into genuine probability sums over disjoint cylinder events.
-/

namespace K5Bridge

open K5Data

lemma push_ne_push (w : String) {c₁ c₂ : Char} (hc : c₁ ≠ c₂) : w.push c₁ ≠ w.push c₂ := by
  intro h
  have h' : w.toList ++ [c₁] = w.toList ++ [c₂] := by
    simpa [String.toList_push] using congrArg String.toList h
  have hs : ([c₁] : List Char) = [c₂] := List.append_cancel_left h'
  have : c₁ = c₂ := by
    have : some c₁ = some c₂ := by simpa using congrArg List.head? hs
    simpa using Option.some.inj this
  exact hc this

lemma push_left_injective {w₁ w₂ : String} {c₁ c₂ : Char} (h : w₁.push c₁ = w₂.push c₂) :
    w₁ = w₂ := by
  have hlist : w₁.toList ++ [c₁] = w₂.toList ++ [c₂] := by
    simpa [String.toList_push] using congrArg String.toList h
  have hlen : w₁.toList.length = w₂.toList.length := by
    have hlen' := congrArg List.length hlist
    -- both sides are `(length prefix) + 1`
    have hlen'' : w₁.toList.length + 1 = w₂.toList.length + 1 := by
      simpa [List.length_append] using hlen'
    exact Nat.add_right_cancel hlen''
  have htake := congrArg (List.take w₁.toList.length) hlist
  have hL : (w₁.toList ++ [c₁]).take w₁.toList.length = w₁.toList := by
    simpa [List.take_length] using
      (List.take_append_of_le_length (l₁ := w₁.toList) (l₂ := [c₁]) (i := w₁.toList.length) le_rfl)
  have hR : (w₂.toList ++ [c₂]).take w₁.toList.length = w₂.toList := by
    have hle : w₁.toList.length ≤ w₂.toList.length := by simpa [hlen] using le_rfl
    have h' :=
      (List.take_append_of_le_length (l₁ := w₂.toList) (l₂ := [c₂]) (i := w₁.toList.length) hle)
    -- `take` of the whole prefix list.
    simpa [hlen, List.take_length] using h'
  have hprefix : w₁.toList = w₂.toList := by
    have htmp := htake
    -- Rewrite both sides of the `take` equality.
    -- (Avoid `simp` here to prevent rewriting `toList.length` back to `String.length`.)
    rw [hL] at htmp
    rw [hR] at htmp
    exact htmp
  exact String.ext hprefix

lemma mem_extensions {w s : String} (hs : s ∈ K5Data.extensions w) :
    s = w.push '0' ∨ s = w.push '1' := by
  classical
  unfold K5Data.extensions at hs
  cases hrev : w.toList.reverse with
  | nil =>
      -- default branch
      simpa [hrev] using hs
  | cons c tail =>
      by_cases hc1 : c = '1'
      · subst hc1
        -- forced `0`
        have : s = w.push '0' := by simpa [hrev] using hs
        exact Or.inl this
      · cases tail with
        | nil =>
            -- default branch
            simpa [hrev, hc1] using hs
        | cons c₂ tail₂ =>
            by_cases hc0 : c = '0'
            · subst hc0
              by_cases hc20 : c₂ = '0'
              · subst hc20
                -- forced `1`
                have : s = w.push '1' := by simpa [hrev, hc1] using hs
                exact Or.inr this
              · -- default branch
                simpa [hrev, hc1, hc20] using hs
            · -- default branch
              simpa [hrev, hc1, hc0] using hs

lemma nodup_extensions (w : String) : (K5Data.extensions w).Nodup := by
  classical
  unfold K5Data.extensions
  have h01 : w.push '0' ≠ w.push '1' := push_ne_push w (c₁ := '0') (c₂ := '1') (by decide)
  cases hrev : w.toList.reverse with
  | nil =>
      -- default branch
      simp [hrev, h01]
  | cons c tail =>
      by_cases hc1 : c = '1'
      · subst hc1
        -- forced `0`
        simp [hrev]
      · cases tail with
        | nil =>
            -- default branch
            simp [hrev, hc1, h01]
        | cons c₂ tail₂ =>
            by_cases hc0 : c = '0'
            · subst hc0
              by_cases hc20 : c₂ = '0'
              · subst hc20
                -- forced `1`
                simp [hrev, hc1]
              · -- default branch
                simp [hrev, hc1, hc20, h01]
            · -- default branch
              simp [hrev, hc1, hc0, h01]

lemma extensions_disjoint_of_ne {w₁ w₂ : String} (h : w₁ ≠ w₂) :
    List.Disjoint (K5Data.extensions w₁) (K5Data.extensions w₂) := by
  intro s hs₁ hs₂
  rcases mem_extensions (w := w₁) (s := s) hs₁ with hs₁' | hs₁'
  · rcases mem_extensions (w := w₂) (s := s) hs₂ with hs₂' | hs₂'
    · have hpush : w₁ = w₂ :=
        push_left_injective (w₁ := w₁) (w₂ := w₂) (c₁ := '0') (c₂ := '0') (h := hs₁'.symm.trans hs₂')
      exact h hpush
    · have hpush : w₁ = w₂ :=
        push_left_injective (w₁ := w₁) (w₂ := w₂) (c₁ := '0') (c₂ := '1') (h := hs₁'.symm.trans hs₂')
      exact h hpush
  · rcases mem_extensions (w := w₂) (s := s) hs₂ with hs₂' | hs₂'
    · have hpush : w₁ = w₂ :=
        push_left_injective (w₁ := w₁) (w₂ := w₂) (c₁ := '1') (c₂ := '0') (h := hs₁'.symm.trans hs₂')
      exact h hpush
    · have hpush : w₁ = w₂ :=
        push_left_injective (w₁ := w₁) (w₂ := w₂) (c₁ := '1') (c₂ := '1') (h := hs₁'.symm.trans hs₂')
      exact h hpush

lemma pairwise_disjoint_on_extensions_of_nodup {l : List String} (hl : l.Nodup) :
    l.Pairwise (Function.onFun List.Disjoint K5Data.extensions) := by
  classical
  induction l with
  | nil =>
      simp
  | cons a l ih =>
      have ha : a ∉ l := (List.nodup_cons.1 hl).1
      have hl' : l.Nodup := (List.nodup_cons.1 hl).2
      have htail : l.Pairwise (Function.onFun List.Disjoint K5Data.extensions) := ih hl'
      refine List.Pairwise.cons ?_ htail
      intro b hb
      have hne : a ≠ b := by
        intro hab
        apply ha
        simpa [hab] using hb
      exact extensions_disjoint_of_ne (w₁ := a) (w₂ := b) hne

lemma nodup_flatMap_extensions {l : List String} (hl : l.Nodup) :
    (l.flatMap K5Data.extensions).Nodup := by
  classical
  refine (List.nodup_flatMap).2 ?_
  refine ⟨?_, pairwise_disjoint_on_extensions_of_nodup hl⟩
  intro w hw
  exact nodup_extensions w

lemma nodup_extendWords {words : Array String} (hwords : words.toList.Nodup) :
    (K5Data.extendWords words).toList.Nodup := by
  classical
  have hflat : (words.toList.flatMap K5Data.extensions).Nodup := nodup_flatMap_extensions hwords
  simpa [K5Data.extendWords, List.toList_toArray] using hflat

lemma nodup_iterate_extendWords {words : Array String} (hwords : words.toList.Nodup) (n : Nat) :
    (Nat.iterate K5Data.extendWords n words).toList.Nodup := by
  induction n generalizing words with
  | zero =>
      simpa [Nat.iterate] using hwords
  | succ n ih =>
      have hwords' : (K5Data.extendWords words).toList.Nodup := nodup_extendWords (words := words) hwords
      simpa [Nat.iterate] using ih (words := K5Data.extendWords words) hwords'

lemma allowedWords_nodup (L : Nat) : (K5Data.allowedWords L).toList.Nodup := by
  classical
  by_cases hL : L = 0
  · subst hL
    simp [K5Data.allowedWords]
  · cases L with
    | zero =>
        cases (hL rfl)
    | succ n =>
        have hbase : ((#["0", "1"] : Array String).toList).Nodup := by native_decide
        -- `allowedWords (n+1) = iterate extendWords n base`.
        have hiter :=
          nodup_iterate_extendWords (words := (#["0", "1"] : Array String)) hbase n
        simpa [K5Data.allowedWords, Nat.succ_ne_zero, Nat.succ_sub_one] using hiter

end K5Bridge

end FiniteDependence.MIS
