import FiniteDependence.MIS.K5Bridge.StepLemmas
import FiniteDependence.MIS.K5Bridge.NoDup

namespace FiniteDependence.MIS

namespace K5Bridge

namespace Model

namespace Step2Sparse

private lemma iterate_succ_apply {α : Type} (f : α → α) (n : Nat) (x : α) :
    Nat.iterate f (n + 1) x = f (Nat.iterate f n x) := by
  induction n generalizing x with
  | zero =>
      simp [Nat.iterate]
  | succ n ih =>
      calc
        Nat.iterate f (n + 2) x = Nat.iterate f (n + 1) (f x) := by
          simp [Nat.iterate, Nat.add_assoc]
        _ = f (Nat.iterate f n (f x)) := ih (x := f x)
        _ = f (Nat.iterate f (n + 1) x) := by
          simp [Nat.iterate, Nat.add_assoc]

private lemma allowedWords_succ_succ (n : Nat) :
    K5Data.allowedWords (n + 2) = K5Data.extendWords (K5Data.allowedWords (n + 1)) := by
  have hn1 : n + 1 ≠ 0 := Nat.succ_ne_zero n
  have hn2 : n + 2 ≠ 0 := Nat.succ_ne_zero (n + 1)
  simp [K5Data.allowedWords, hn1, hn2, iterate_succ_apply, Nat.add_assoc, Nat.add_left_comm,
    Nat.add_comm]

private lemma mem_allowedWordsFinset_succ_succ {n : Nat} {s : String} :
    s ∈ allowedWordsFinset (n + 2) ↔ ∃ w ∈ allowedWordsFinset (n + 1), s ∈ K5Data.extensions w := by
  constructor
  · intro hs
    have hs' : s ∈ K5Data.allowedWords (n + 2) :=
      (mem_allowedWordsFinset_iff (L := n + 2) (s := s)).1 hs
    have hs'' : s ∈ K5Data.extendWords (K5Data.allowedWords (n + 1)) := by
      simpa [allowedWords_succ_succ (n := n)] using hs'
    have hsFlat : s ∈ (K5Data.allowedWords (n + 1)).toList.flatMap K5Data.extensions := by
      simpa [K5Data.extendWords, List.toList_toArray] using hs''
    rcases List.mem_flatMap.mp hsFlat with ⟨w, hw, hsExt⟩
    exact ⟨w, (mem_allowedWordsFinset_iff (L := n + 1) (s := w)).2 (by simpa using hw), hsExt⟩
  · rintro ⟨w, hw, hsExt⟩
    have hw' : w ∈ K5Data.allowedWords (n + 1) :=
      (mem_allowedWordsFinset_iff (L := n + 1) (s := w)).1 hw
    have hwList : w ∈ (K5Data.allowedWords (n + 1)).toList := by
      simpa using hw'
    have hsFlat : s ∈ (K5Data.allowedWords (n + 1)).toList.flatMap K5Data.extensions :=
      List.mem_flatMap.mpr ⟨w, hwList, hsExt⟩
    have hs'' : s ∈ K5Data.extendWords (K5Data.allowedWords (n + 1)) := by
      simpa [K5Data.extendWords, List.toList_toArray] using hsFlat
    exact (mem_allowedWordsFinset_iff (L := n + 2) (s := s)).2 <| by
      simpa [allowedWords_succ_succ (n := n)] using hs''

private lemma prefixOf_push_of_le (w : String) (c : Char) {m : Nat} (hm : m ≤ w.length) :
    prefixOf (w.push c) m = prefixOf w m := by
  apply String.ext
  have hm' : m ≤ w.toList.length := by
    simpa [String.length_toList] using hm
  have htake : (w.toList ++ [c]).take m = w.toList.take m := by
    simpa using
      (List.take_append_of_le_length (l₁ := w.toList) (l₂ := [c]) (i := m) hm')
  simpa [prefixOf, String.toList_push] using htake

private lemma suffixFrom_push_of_le (w : String) (c : Char) {k : Nat} (hk : k ≤ w.length) :
    suffixFrom (w.push c) k = (suffixFrom w k).push c := by
  apply String.ext
  have hk' : k ≤ w.toList.length := by
    simpa [String.length_toList] using hk
  have hdrop : (w.toList ++ [c]).drop k = w.toList.drop k ++ [c] := by
    simpa using
      (List.drop_append_of_le_length (l₁ := w.toList) (l₂ := [c]) (i := k) hk')
  simpa [suffixFrom, String.toList_push] using hdrop

private lemma prefixOf_self (w : String) : prefixOf w w.length = w := by
  apply String.ext
  simp [prefixOf, String.length_toList]

private lemma suffixFrom_self (w : String) : suffixFrom w w.length = "" := by
  apply String.ext
  simp [suffixFrom, String.length_toList]

private lemma prefixOf_of_mem_extensions {w s : String} {m : Nat}
    (hs : s ∈ K5Data.extensions w) (hm : m ≤ w.length) :
    prefixOf s m = prefixOf w m := by
  rcases mem_extensions (w := w) (s := s) hs with rfl | rfl
  · exact prefixOf_push_of_le (w := w) (c := '0') hm
  · exact prefixOf_push_of_le (w := w) (c := '1') hm

private lemma suffixFrom_of_mem_extensions {w s : String} {k : Nat}
    (hs : s ∈ K5Data.extensions w) (hk : k ≤ w.length) :
    ∃ c : Char, suffixFrom s k = (suffixFrom w k).push c := by
  rcases mem_extensions (w := w) (s := s) hs with rfl | rfl
  · exact ⟨'0', suffixFrom_push_of_le (w := w) (c := '0') hk⟩
  · exact ⟨'1', suffixFrom_push_of_le (w := w) (c := '1') hk⟩

private lemma filter_prefix_exact {m : Nat} {x : String} (hx : x ∈ allowedWordsFinset m) :
    (allowedWordsFinset m).filter (fun w => prefixOf w m = x) = ({x} : Finset String) := by
  ext w
  constructor
  · intro hw
    rcases Finset.mem_filter.1 hw with ⟨hw_mem, hw_pref⟩
    have hw_allowed : w ∈ K5Data.allowedWords m :=
      (mem_allowedWordsFinset_iff (L := m) (s := w)).1 hw_mem
    have hw_len : w.length = m := length_of_mem_allowedWords (L := m) (s := w) hw_allowed
    have hw_self : prefixOf w m = w := by
      simpa [hw_len] using prefixOf_self w
    have : w = x := by
      simpa [hw_self] using hw_pref
    simpa [this]
  · intro hw
    have : w = x := by simpa using hw
    subst w
    have hx_allowed : x ∈ K5Data.allowedWords m :=
      (mem_allowedWordsFinset_iff (L := m) (s := x)).1 hx
    have hx_len : x.length = m := length_of_mem_allowedWords (L := m) (s := x) hx_allowed
    exact Finset.mem_filter.2 ⟨hx, by simpa [hx_len] using prefixOf_self x⟩

private lemma filter_pref_suf_empty {m L : Nat} {x : String} (hL : L = m + 5) :
    (allowedWordsFinset L).filter (fun w => prefixOf w m = x ∧ suffixFrom w (m + 5) = "") =
      (allowedWordsFinset L).filter (fun w => prefixOf w m = x) := by
  ext w
  constructor
  · intro hw
    exact Finset.mem_filter.2 ⟨(Finset.mem_filter.1 hw).1, (Finset.mem_filter.1 hw).2.1⟩
  · intro hw
    rcases Finset.mem_filter.1 hw with ⟨hw_mem, hw_pref⟩
    have hw_allowed : w ∈ K5Data.allowedWords L :=
      (mem_allowedWordsFinset_iff (L := L) (s := w)).1 hw_mem
    have hw_len : w.length = L := length_of_mem_allowedWords (L := L) (s := w) hw_allowed
    have hw_suf : suffixFrom w (m + 5) = "" := by
      simpa [hL, hw_len] using suffixFrom_self w
    exact Finset.mem_filter.2 ⟨hw_mem, ⟨hw_pref, hw_suf⟩⟩

private lemma filter_prefix_step {m n : Nat} {x : String} (hm : m ≤ n + 1) :
    (allowedWordsFinset (n + 2)).filter (fun s => prefixOf s m = x) =
      (((allowedWordsFinset (n + 1)).filter (fun w => prefixOf w m = x)).biUnion
        fun w => (K5Data.extensions w).toFinset) := by
  ext s
  constructor
  · intro hs
    rcases Finset.mem_filter.1 hs with ⟨hs_mem, hs_pref⟩
    rcases (mem_allowedWordsFinset_succ_succ (n := n) (s := s)).1 hs_mem with ⟨w, hw, hs_ext⟩
    have hw_pref : prefixOf w m = x := by
      have hw_allowed : w ∈ K5Data.allowedWords (n + 1) :=
        (mem_allowedWordsFinset_iff (L := n + 1) (s := w)).1 hw
      have hw_len : w.length = n + 1 := length_of_mem_allowedWords (L := n + 1) (s := w) hw_allowed
      have hm' : m ≤ w.length := by
        simpa [hw_len] using hm
      have hs_pw : prefixOf s m = prefixOf w m := prefixOf_of_mem_extensions hs_ext hm'
      simpa [hs_pref] using hs_pw.symm
    exact Finset.mem_biUnion.2 ⟨w, Finset.mem_filter.2 ⟨hw, hw_pref⟩, by
      simpa using hs_ext⟩
  · intro hs
    rcases Finset.mem_biUnion.1 hs with ⟨w, hw, hs_ext⟩
    rcases Finset.mem_filter.1 hw with ⟨hw_mem, hw_pref⟩
    have hs_mem : s ∈ allowedWordsFinset (n + 2) :=
      (mem_allowedWordsFinset_succ_succ (n := n) (s := s)).2 ⟨w, hw_mem, by
        simpa using hs_ext⟩
    have hw_allowed : w ∈ K5Data.allowedWords (n + 1) :=
      (mem_allowedWordsFinset_iff (L := n + 1) (s := w)).1 hw_mem
    have hw_len : w.length = n + 1 := length_of_mem_allowedWords (L := n + 1) (s := w) hw_allowed
    have hm' : m ≤ w.length := by
      simpa [hw_len] using hm
    have hs_pw : prefixOf s m = prefixOf w m := prefixOf_of_mem_extensions (by
      simpa using hs_ext) hm'
    exact Finset.mem_filter.2 ⟨hs_mem, by simpa [hw_pref] using hs_pw⟩

private lemma filter_pref_suf_step {m n : Nat} {x u : String} {c : Char}
    (hm : m ≤ n + 1) (hk : m + 5 ≤ n + 1) :
    (allowedWordsFinset (n + 2)).filter
        (fun s => prefixOf s m = x ∧ suffixFrom s (m + 5) = u.push c) =
      (((allowedWordsFinset (n + 1)).filter
          (fun w => prefixOf w m = x ∧ suffixFrom w (m + 5) = u)).biUnion
        fun w => ((K5Data.extensions w).toFinset).filter
          (fun s => suffixFrom s (m + 5) = u.push c)) := by
  ext s
  constructor
  · intro hs
    rcases Finset.mem_filter.1 hs with ⟨hs_mem, hs_pred⟩
    rcases (mem_allowedWordsFinset_succ_succ (n := n) (s := s)).1 hs_mem with ⟨w, hw, hs_ext⟩
    have hw_allowed : w ∈ K5Data.allowedWords (n + 1) :=
      (mem_allowedWordsFinset_iff (L := n + 1) (s := w)).1 hw
    have hw_len : w.length = n + 1 := length_of_mem_allowedWords (L := n + 1) (s := w) hw_allowed
    have hm' : m ≤ w.length := by
      simpa [hw_len] using hm
    have hk' : m + 5 ≤ w.length := by
      simpa [hw_len] using hk
    have hw_pref : prefixOf w m = x := by
      have hs_pw : prefixOf s m = prefixOf w m := prefixOf_of_mem_extensions hs_ext hm'
      simpa [hs_pred.1] using hs_pw.symm
    have hw_suf : suffixFrom w (m + 5) = u := by
      rcases suffixFrom_of_mem_extensions hs_ext hk' with ⟨d, hs_suf⟩
      have hs_eq : u.push c = (suffixFrom w (m + 5)).push d := by
        simpa [hs_pred.2] using hs_suf
      exact (push_left_injective hs_eq).symm
    exact Finset.mem_biUnion.2 ⟨w, Finset.mem_filter.2 ⟨hw, ⟨hw_pref, hw_suf⟩⟩,
      Finset.mem_filter.2 ⟨by simpa using hs_ext, hs_pred.2⟩⟩
  · intro hs
    rcases Finset.mem_biUnion.1 hs with ⟨w, hw, hs⟩
    rcases Finset.mem_filter.1 hw with ⟨hw_mem, hw_pred⟩
    rcases Finset.mem_filter.1 hs with ⟨hs_ext, hs_suf⟩
    have hs_mem : s ∈ allowedWordsFinset (n + 2) :=
      (mem_allowedWordsFinset_succ_succ (n := n) (s := s)).2 ⟨w, hw_mem, by
        simpa using hs_ext⟩
    have hw_allowed : w ∈ K5Data.allowedWords (n + 1) :=
      (mem_allowedWordsFinset_iff (L := n + 1) (s := w)).1 hw_mem
    have hw_len : w.length = n + 1 := length_of_mem_allowedWords (L := n + 1) (s := w) hw_allowed
    have hm' : m ≤ w.length := by
      simpa [hw_len] using hm
    have hs_pref : prefixOf s m = x := by
      have hs_pw : prefixOf s m = prefixOf w m :=
        prefixOf_of_mem_extensions (by simpa using hs_ext) hm'
      simpa [hw_pred.1] using hs_pw
    exact Finset.mem_filter.2 ⟨hs_mem, ⟨hs_pref, hs_suf⟩⟩

theorem filter_1010010101_1_eq :
    (allowedWordsFinset (10 + 5 + 1)).filter
        (fun w => prefixOf w 10 = ("1010010101" : String) ∧ suffixFrom w (10 + 5) = ("1" : String)) =
      ({("1010010101001001" : String), "1010010101010101"} : Finset String) := by
  have h10_mem : ("1010010101" : String) ∈ allowedWordsFinset 10 := by decide
  have h10 :
      (allowedWordsFinset 10).filter (fun w => prefixOf w 10 = ("1010010101" : String)) =
        ({("1010010101" : String)} : Finset String) :=
    filter_prefix_exact h10_mem
  have h11 :
      (allowedWordsFinset 11).filter (fun w => prefixOf w 10 = ("1010010101" : String)) =
        ({("10100101010" : String)} : Finset String) := by
    rw [filter_prefix_step (m := 10) (n := 9) (x := ("1010010101" : String)) (by decide), h10]
    decide
  have h12 :
      (allowedWordsFinset 12).filter (fun w => prefixOf w 10 = ("1010010101" : String)) =
        ({("101001010100" : String), "101001010101"} : Finset String) := by
    rw [filter_prefix_step (m := 10) (n := 10) (x := ("1010010101" : String)) (by decide), h11]
    decide
  have h13 :
      (allowedWordsFinset 13).filter (fun w => prefixOf w 10 = ("1010010101" : String)) =
        ({("1010010101001" : String), "1010010101010"} : Finset String) := by
    rw [filter_prefix_step (m := 10) (n := 11) (x := ("1010010101" : String)) (by decide), h12]
    decide
  have h14 :
      (allowedWordsFinset 14).filter (fun w => prefixOf w 10 = ("1010010101" : String)) =
        ({("10100101010010" : String), "10100101010100", "10100101010101"} : Finset String) := by
    rw [filter_prefix_step (m := 10) (n := 12) (x := ("1010010101" : String)) (by decide), h13]
    decide
  have h15 :
      (allowedWordsFinset 15).filter (fun w => prefixOf w 10 = ("1010010101" : String)) =
        ({("101001010100100" : String), "101001010100101", "101001010101001", "101001010101010"} :
          Finset String) := by
    rw [filter_prefix_step (m := 10) (n := 13) (x := ("1010010101" : String)) (by decide), h14]
    decide
  have h16_pref :
      (allowedWordsFinset 16).filter (fun w => prefixOf w 10 = ("1010010101" : String)) =
        ({("1010010101001001" : String), "1010010101001010", "1010010101010010",
          "1010010101010100", "1010010101010101"} : Finset String) := by
    rw [filter_prefix_step (m := 10) (n := 14) (x := ("1010010101" : String)) (by decide), h15]
    decide
  calc
    (allowedWordsFinset 16).filter
        (fun w => prefixOf w 10 = ("1010010101" : String) ∧ suffixFrom w 15 = ("1" : String)) =
      ((allowedWordsFinset 16).filter (fun w => prefixOf w 10 = ("1010010101" : String))).filter
        (fun w => suffixFrom w 15 = ("1" : String)) := by
          ext w
          simp [Finset.mem_filter, and_assoc, and_left_comm, and_comm]
    _ = ({("1010010101001001" : String), "1010010101001010", "1010010101010010",
          "1010010101010100", "1010010101010101"} : Finset String).filter
        (fun w => suffixFrom w 15 = ("1" : String)) := by
          rw [h16_pref]
    _ = ({("1010010101001001" : String), "1010010101010101"} : Finset String) := by
          decide

theorem filter_00100_1010010100_eq :
    (allowedWordsFinset (5 + 5 + 10)).filter
        (fun w => prefixOf w 5 = ("00100" : String) ∧ suffixFrom w (5 + 5) = ("1010010100" : String)) =
      ({("00100100101010010100" : String), "00100101001010010100"} : Finset String) := by
  have h5_mem : ("00100" : String) ∈ allowedWordsFinset 5 := by decide
  have h5 :
      (allowedWordsFinset 5).filter (fun w => prefixOf w 5 = ("00100" : String)) =
        ({("00100" : String)} : Finset String) :=
    filter_prefix_exact h5_mem
  have h6 :
      (allowedWordsFinset 6).filter (fun w => prefixOf w 5 = ("00100" : String)) =
        ({("001001" : String)} : Finset String) := by
    rw [filter_prefix_step (m := 5) (n := 4) (x := ("00100" : String)) (by decide), h5]
    decide
  have h7 :
      (allowedWordsFinset 7).filter (fun w => prefixOf w 5 = ("00100" : String)) =
        ({("0010010" : String)} : Finset String) := by
    rw [filter_prefix_step (m := 5) (n := 5) (x := ("00100" : String)) (by decide), h6]
    decide
  have h8 :
      (allowedWordsFinset 8).filter (fun w => prefixOf w 5 = ("00100" : String)) =
        ({("00100100" : String), "00100101"} : Finset String) := by
    rw [filter_prefix_step (m := 5) (n := 6) (x := ("00100" : String)) (by decide), h7]
    decide
  have h9 :
      (allowedWordsFinset 9).filter (fun w => prefixOf w 5 = ("00100" : String)) =
        ({("001001001" : String), "001001010"} : Finset String) := by
    rw [filter_prefix_step (m := 5) (n := 7) (x := ("00100" : String)) (by decide), h8]
    decide
  have h10 :
      (allowedWordsFinset 10).filter (fun w => prefixOf w 5 = ("00100" : String)) =
        ({("0010010010" : String), "0010010100", "0010010101"} : Finset String) := by
    rw [filter_prefix_step (m := 5) (n := 8) (x := ("00100" : String)) (by decide), h9]
    decide
  have h10_empty :
      (allowedWordsFinset 10).filter
          (fun w => prefixOf w 5 = ("00100" : String) ∧ suffixFrom w 10 = ("" : String)) =
        ({("0010010010" : String), "0010010100", "0010010101"} : Finset String) := by
    rw [filter_pref_suf_empty (m := 5) (L := 10) (x := ("00100" : String)) (by decide), h10]
  have h11 :
      (allowedWordsFinset 11).filter
          (fun w => prefixOf w 5 = ("00100" : String) ∧ suffixFrom w 10 = ("1" : String)) =
        ({("00100100101" : String), "00100101001"} : Finset String) := by
    have hstep := filter_pref_suf_step (m := 5) (n := 9) (x := ("00100" : String)) (u := ("" : String))
      (c := '1') (by decide) (by decide)
    rw [show
      (allowedWordsFinset 11).filter
          (fun w => prefixOf w 5 = ("00100" : String) ∧ suffixFrom w 10 = ("1" : String)) =
        (((allowedWordsFinset 10).filter
            (fun w => prefixOf w 5 = ("00100" : String) ∧ suffixFrom w 10 = ("" : String))).biUnion
          fun w => ((K5Data.extensions w).toFinset).filter
            (fun s => suffixFrom s 10 = ("1" : String))) from by
          simpa using hstep]
    rw [h10_empty]
    decide
  have h12 :
      (allowedWordsFinset 12).filter
          (fun w => prefixOf w 5 = ("00100" : String) ∧ suffixFrom w 10 = ("10" : String)) =
        ({("001001001010" : String), "001001010010"} : Finset String) := by
    rw [show
      (allowedWordsFinset 12).filter
          (fun w => prefixOf w 5 = ("00100" : String) ∧ suffixFrom w 10 = ("10" : String)) =
        (((allowedWordsFinset 11).filter
            (fun w => prefixOf w 5 = ("00100" : String) ∧ suffixFrom w 10 = ("1" : String))).biUnion
          fun w => ((K5Data.extensions w).toFinset).filter
            (fun s => suffixFrom s 10 = ("10" : String))) from by
          simpa using
            (filter_pref_suf_step (m := 5) (n := 10) (x := ("00100" : String)) (u := ("1" : String))
              (c := '0') (by decide) (by decide))]
    rw [h11]
    decide
  have h13 :
      (allowedWordsFinset 13).filter
          (fun w => prefixOf w 5 = ("00100" : String) ∧ suffixFrom w 10 = ("101" : String)) =
        ({("0010010010101" : String), "0010010100101"} : Finset String) := by
    rw [show
      (allowedWordsFinset 13).filter
          (fun w => prefixOf w 5 = ("00100" : String) ∧ suffixFrom w 10 = ("101" : String)) =
        (((allowedWordsFinset 12).filter
            (fun w => prefixOf w 5 = ("00100" : String) ∧ suffixFrom w 10 = ("10" : String))).biUnion
          fun w => ((K5Data.extensions w).toFinset).filter
            (fun s => suffixFrom s 10 = ("101" : String))) from by
          simpa using
            (filter_pref_suf_step (m := 5) (n := 11) (x := ("00100" : String)) (u := ("10" : String))
              (c := '1') (by decide) (by decide))]
    rw [h12]
    decide
  have h14 :
      (allowedWordsFinset 14).filter
          (fun w => prefixOf w 5 = ("00100" : String) ∧ suffixFrom w 10 = ("1010" : String)) =
        ({("00100100101010" : String), "00100101001010"} : Finset String) := by
    rw [show
      (allowedWordsFinset 14).filter
          (fun w => prefixOf w 5 = ("00100" : String) ∧ suffixFrom w 10 = ("1010" : String)) =
        (((allowedWordsFinset 13).filter
            (fun w => prefixOf w 5 = ("00100" : String) ∧ suffixFrom w 10 = ("101" : String))).biUnion
          fun w => ((K5Data.extensions w).toFinset).filter
            (fun s => suffixFrom s 10 = ("1010" : String))) from by
          simpa using
            (filter_pref_suf_step (m := 5) (n := 12) (x := ("00100" : String)) (u := ("101" : String))
              (c := '0') (by decide) (by decide))]
    rw [h13]
    decide
  have h15 :
      (allowedWordsFinset 15).filter
          (fun w => prefixOf w 5 = ("00100" : String) ∧ suffixFrom w 10 = ("10100" : String)) =
        ({("001001001010100" : String), "001001010010100"} : Finset String) := by
    rw [show
      (allowedWordsFinset 15).filter
          (fun w => prefixOf w 5 = ("00100" : String) ∧ suffixFrom w 10 = ("10100" : String)) =
        (((allowedWordsFinset 14).filter
            (fun w => prefixOf w 5 = ("00100" : String) ∧ suffixFrom w 10 = ("1010" : String))).biUnion
          fun w => ((K5Data.extensions w).toFinset).filter
            (fun s => suffixFrom s 10 = ("10100" : String))) from by
          simpa using
            (filter_pref_suf_step (m := 5) (n := 13) (x := ("00100" : String)) (u := ("1010" : String))
              (c := '0') (by decide) (by decide))]
    rw [h14]
    decide
  have h16 :
      (allowedWordsFinset 16).filter
          (fun w => prefixOf w 5 = ("00100" : String) ∧ suffixFrom w 10 = ("101001" : String)) =
        ({("0010010010101001" : String), "0010010100101001"} : Finset String) := by
    rw [show
      (allowedWordsFinset 16).filter
          (fun w => prefixOf w 5 = ("00100" : String) ∧ suffixFrom w 10 = ("101001" : String)) =
        (((allowedWordsFinset 15).filter
            (fun w => prefixOf w 5 = ("00100" : String) ∧ suffixFrom w 10 = ("10100" : String))).biUnion
          fun w => ((K5Data.extensions w).toFinset).filter
            (fun s => suffixFrom s 10 = ("101001" : String))) from by
          simpa using
            (filter_pref_suf_step (m := 5) (n := 14) (x := ("00100" : String)) (u := ("10100" : String))
              (c := '1') (by decide) (by decide))]
    rw [h15]
    decide
  have h17 :
      (allowedWordsFinset 17).filter
          (fun w => prefixOf w 5 = ("00100" : String) ∧ suffixFrom w 10 = ("1010010" : String)) =
        ({("00100100101010010" : String), "00100101001010010"} : Finset String) := by
    rw [show
      (allowedWordsFinset 17).filter
          (fun w => prefixOf w 5 = ("00100" : String) ∧ suffixFrom w 10 = ("1010010" : String)) =
        (((allowedWordsFinset 16).filter
            (fun w => prefixOf w 5 = ("00100" : String) ∧ suffixFrom w 10 = ("101001" : String))).biUnion
          fun w => ((K5Data.extensions w).toFinset).filter
            (fun s => suffixFrom s 10 = ("1010010" : String))) from by
          simpa using
            (filter_pref_suf_step (m := 5) (n := 15) (x := ("00100" : String)) (u := ("101001" : String))
              (c := '0') (by decide) (by decide))]
    rw [h16]
    decide
  have h18 :
      (allowedWordsFinset 18).filter
          (fun w => prefixOf w 5 = ("00100" : String) ∧ suffixFrom w 10 = ("10100101" : String)) =
        ({("001001001010100101" : String), "001001010010100101"} : Finset String) := by
    rw [show
      (allowedWordsFinset 18).filter
          (fun w => prefixOf w 5 = ("00100" : String) ∧ suffixFrom w 10 = ("10100101" : String)) =
        (((allowedWordsFinset 17).filter
            (fun w => prefixOf w 5 = ("00100" : String) ∧ suffixFrom w 10 = ("1010010" : String))).biUnion
          fun w => ((K5Data.extensions w).toFinset).filter
            (fun s => suffixFrom s 10 = ("10100101" : String))) from by
          simpa using
            (filter_pref_suf_step (m := 5) (n := 16) (x := ("00100" : String)) (u := ("1010010" : String))
              (c := '1') (by decide) (by decide))]
    rw [h17]
    decide
  have h19 :
      (allowedWordsFinset 19).filter
          (fun w => prefixOf w 5 = ("00100" : String) ∧ suffixFrom w 10 = ("101001010" : String)) =
        ({("0010010010101001010" : String), "0010010100101001010"} : Finset String) := by
    rw [show
      (allowedWordsFinset 19).filter
          (fun w => prefixOf w 5 = ("00100" : String) ∧ suffixFrom w 10 = ("101001010" : String)) =
        (((allowedWordsFinset 18).filter
            (fun w => prefixOf w 5 = ("00100" : String) ∧ suffixFrom w 10 = ("10100101" : String))).biUnion
          fun w => ((K5Data.extensions w).toFinset).filter
            (fun s => suffixFrom s 10 = ("101001010" : String))) from by
          simpa using
            (filter_pref_suf_step (m := 5) (n := 17) (x := ("00100" : String)) (u := ("10100101" : String))
              (c := '0') (by decide) (by decide))]
    rw [h18]
    decide
  have h20 :
      (allowedWordsFinset 20).filter
          (fun w => prefixOf w 5 = ("00100" : String) ∧ suffixFrom w 10 = ("1010010100" : String)) =
        ({("00100100101010010100" : String), "00100101001010010100"} : Finset String) := by
    rw [show
      (allowedWordsFinset 20).filter
          (fun w => prefixOf w 5 = ("00100" : String) ∧ suffixFrom w 10 = ("1010010100" : String)) =
        (((allowedWordsFinset 19).filter
            (fun w => prefixOf w 5 = ("00100" : String) ∧ suffixFrom w 10 = ("101001010" : String))).biUnion
          fun w => ((K5Data.extensions w).toFinset).filter
            (fun s => suffixFrom s 10 = ("1010010100" : String))) from by
          simpa using
            (filter_pref_suf_step (m := 5) (n := 18) (x := ("00100" : String)) (u := ("101001010" : String))
              (c := '0') (by decide) (by decide))]
    rw [h19]
    decide
  simpa [Nat.add_assoc] using h20

theorem filter_00100100_0010100_eq :
    (allowedWordsFinset (8 + 5 + 7)).filter
        (fun w => prefixOf w 8 = ("00100100" : String) ∧ suffixFrom w (8 + 5) = ("0010100" : String)) =
      ({("00100100101010010100" : String)} : Finset String) := by
  have h8_mem : ("00100100" : String) ∈ allowedWordsFinset 8 := by decide
  have h8 :
      (allowedWordsFinset 8).filter (fun w => prefixOf w 8 = ("00100100" : String)) =
        ({("00100100" : String)} : Finset String) :=
    filter_prefix_exact h8_mem
  have h9 :
      (allowedWordsFinset 9).filter (fun w => prefixOf w 8 = ("00100100" : String)) =
        ({("001001001" : String)} : Finset String) := by
    rw [filter_prefix_step (m := 8) (n := 7) (x := ("00100100" : String)) (by decide), h8]
    decide
  have h10 :
      (allowedWordsFinset 10).filter (fun w => prefixOf w 8 = ("00100100" : String)) =
        ({("0010010010" : String)} : Finset String) := by
    rw [filter_prefix_step (m := 8) (n := 8) (x := ("00100100" : String)) (by decide), h9]
    decide
  have h11 :
      (allowedWordsFinset 11).filter (fun w => prefixOf w 8 = ("00100100" : String)) =
        ({("00100100100" : String), "00100100101"} : Finset String) := by
    rw [filter_prefix_step (m := 8) (n := 9) (x := ("00100100" : String)) (by decide), h10]
    decide
  have h12 :
      (allowedWordsFinset 12).filter (fun w => prefixOf w 8 = ("00100100" : String)) =
        ({("001001001001" : String), "001001001010"} : Finset String) := by
    rw [filter_prefix_step (m := 8) (n := 10) (x := ("00100100" : String)) (by decide), h11]
    decide
  have h13 :
      (allowedWordsFinset 13).filter (fun w => prefixOf w 8 = ("00100100" : String)) =
        ({("0010010010010" : String), "0010010010100", "0010010010101"} : Finset String) := by
    rw [filter_prefix_step (m := 8) (n := 11) (x := ("00100100" : String)) (by decide), h12]
    decide
  have h13_empty :
      (allowedWordsFinset 13).filter
          (fun w => prefixOf w 8 = ("00100100" : String) ∧ suffixFrom w 13 = ("" : String)) =
        ({("0010010010010" : String), "0010010010100", "0010010010101"} : Finset String) := by
    rw [filter_pref_suf_empty (m := 8) (L := 13) (x := ("00100100" : String)) (by decide), h13]
  have h14 :
      (allowedWordsFinset 14).filter
          (fun w => prefixOf w 8 = ("00100100" : String) ∧ suffixFrom w 13 = ("0" : String)) =
        ({("00100100100100" : String), "00100100101010"} : Finset String) := by
    rw [show
      (allowedWordsFinset 14).filter
          (fun w => prefixOf w 8 = ("00100100" : String) ∧ suffixFrom w 13 = ("0" : String)) =
        (((allowedWordsFinset 13).filter
            (fun w => prefixOf w 8 = ("00100100" : String) ∧ suffixFrom w 13 = ("" : String))).biUnion
          fun w => ((K5Data.extensions w).toFinset).filter
            (fun s => suffixFrom s 13 = ("0" : String))) from by
          simpa using
            (filter_pref_suf_step (m := 8) (n := 12) (x := ("00100100" : String)) (u := ("" : String))
              (c := '0') (by decide) (by decide))]
    rw [h13_empty]
    decide
  have h15 :
      (allowedWordsFinset 15).filter
          (fun w => prefixOf w 8 = ("00100100" : String) ∧ suffixFrom w 13 = ("00" : String)) =
        ({("001001001010100" : String)} : Finset String) := by
    rw [show
      (allowedWordsFinset 15).filter
          (fun w => prefixOf w 8 = ("00100100" : String) ∧ suffixFrom w 13 = ("00" : String)) =
        (((allowedWordsFinset 14).filter
            (fun w => prefixOf w 8 = ("00100100" : String) ∧ suffixFrom w 13 = ("0" : String))).biUnion
          fun w => ((K5Data.extensions w).toFinset).filter
            (fun s => suffixFrom s 13 = ("00" : String))) from by
          simpa using
            (filter_pref_suf_step (m := 8) (n := 13) (x := ("00100100" : String)) (u := ("0" : String))
              (c := '0') (by decide) (by decide))]
    rw [h14]
    decide
  have h16 :
      (allowedWordsFinset 16).filter
          (fun w => prefixOf w 8 = ("00100100" : String) ∧ suffixFrom w 13 = ("001" : String)) =
        ({("0010010010101001" : String)} : Finset String) := by
    rw [show
      (allowedWordsFinset 16).filter
          (fun w => prefixOf w 8 = ("00100100" : String) ∧ suffixFrom w 13 = ("001" : String)) =
        (((allowedWordsFinset 15).filter
            (fun w => prefixOf w 8 = ("00100100" : String) ∧ suffixFrom w 13 = ("00" : String))).biUnion
          fun w => ((K5Data.extensions w).toFinset).filter
            (fun s => suffixFrom s 13 = ("001" : String))) from by
          simpa using
            (filter_pref_suf_step (m := 8) (n := 14) (x := ("00100100" : String)) (u := ("00" : String))
              (c := '1') (by decide) (by decide))]
    rw [h15]
    decide
  have h17 :
      (allowedWordsFinset 17).filter
          (fun w => prefixOf w 8 = ("00100100" : String) ∧ suffixFrom w 13 = ("0010" : String)) =
        ({("00100100101010010" : String)} : Finset String) := by
    rw [show
      (allowedWordsFinset 17).filter
          (fun w => prefixOf w 8 = ("00100100" : String) ∧ suffixFrom w 13 = ("0010" : String)) =
        (((allowedWordsFinset 16).filter
            (fun w => prefixOf w 8 = ("00100100" : String) ∧ suffixFrom w 13 = ("001" : String))).biUnion
          fun w => ((K5Data.extensions w).toFinset).filter
            (fun s => suffixFrom s 13 = ("0010" : String))) from by
          simpa using
            (filter_pref_suf_step (m := 8) (n := 15) (x := ("00100100" : String)) (u := ("001" : String))
              (c := '0') (by decide) (by decide))]
    rw [h16]
    decide
  have h18 :
      (allowedWordsFinset 18).filter
          (fun w => prefixOf w 8 = ("00100100" : String) ∧ suffixFrom w 13 = ("00101" : String)) =
        ({("001001001010100101" : String)} : Finset String) := by
    rw [show
      (allowedWordsFinset 18).filter
          (fun w => prefixOf w 8 = ("00100100" : String) ∧ suffixFrom w 13 = ("00101" : String)) =
        (((allowedWordsFinset 17).filter
            (fun w => prefixOf w 8 = ("00100100" : String) ∧ suffixFrom w 13 = ("0010" : String))).biUnion
          fun w => ((K5Data.extensions w).toFinset).filter
            (fun s => suffixFrom s 13 = ("00101" : String))) from by
          simpa using
            (filter_pref_suf_step (m := 8) (n := 16) (x := ("00100100" : String)) (u := ("0010" : String))
              (c := '1') (by decide) (by decide))]
    rw [h17]
    decide
  have h19 :
      (allowedWordsFinset 19).filter
          (fun w => prefixOf w 8 = ("00100100" : String) ∧ suffixFrom w 13 = ("001010" : String)) =
        ({("0010010010101001010" : String)} : Finset String) := by
    rw [show
      (allowedWordsFinset 19).filter
          (fun w => prefixOf w 8 = ("00100100" : String) ∧ suffixFrom w 13 = ("001010" : String)) =
        (((allowedWordsFinset 18).filter
            (fun w => prefixOf w 8 = ("00100100" : String) ∧ suffixFrom w 13 = ("00101" : String))).biUnion
          fun w => ((K5Data.extensions w).toFinset).filter
            (fun s => suffixFrom s 13 = ("001010" : String))) from by
          simpa using
            (filter_pref_suf_step (m := 8) (n := 17) (x := ("00100100" : String)) (u := ("00101" : String))
              (c := '0') (by decide) (by decide))]
    rw [h18]
    decide
  have h20 :
      (allowedWordsFinset 20).filter
          (fun w => prefixOf w 8 = ("00100100" : String) ∧ suffixFrom w 13 = ("0010100" : String)) =
        ({("00100100101010010100" : String)} : Finset String) := by
    rw [show
      (allowedWordsFinset 20).filter
          (fun w => prefixOf w 8 = ("00100100" : String) ∧ suffixFrom w 13 = ("0010100" : String)) =
        (((allowedWordsFinset 19).filter
            (fun w => prefixOf w 8 = ("00100100" : String) ∧ suffixFrom w 13 = ("001010" : String))).biUnion
          fun w => ((K5Data.extensions w).toFinset).filter
            (fun s => suffixFrom s 13 = ("0010100" : String))) from by
          simpa using
            (filter_pref_suf_step (m := 8) (n := 18) (x := ("00100100" : String)) (u := ("001010" : String))
              (c := '0') (by decide) (by decide))]
    rw [h19]
    decide
  simpa [Nat.add_assoc] using h20

end Step2Sparse

end Model

end K5Bridge

end FiniteDependence.MIS
