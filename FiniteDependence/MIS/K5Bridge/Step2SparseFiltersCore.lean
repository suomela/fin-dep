import FiniteDependence.MIS.K5Bridge.StepLemmas
import FiniteDependence.MIS.K5Bridge.NoDup

namespace FiniteDependence.MIS

namespace K5Bridge

namespace Model

namespace Step2Sparse

lemma iterate_succ_apply {α : Type} (f : α → α) (n : Nat) (x : α) :
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

lemma allowedWords_succ_succ (n : Nat) :
    K5Data.allowedWords (n + 2) = K5Data.extendWords (K5Data.allowedWords (n + 1)) := by
  have hn1 : n + 1 ≠ 0 := Nat.succ_ne_zero n
  have hn2 : n + 2 ≠ 0 := Nat.succ_ne_zero (n + 1)
  simp [K5Data.allowedWords, hn1, hn2, iterate_succ_apply, Nat.add_assoc, Nat.add_left_comm,
    Nat.add_comm]

lemma mem_allowedWordsFinset_succ_succ {n : Nat} {s : String} :
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

lemma prefixOf_push_of_le (w : String) (c : Char) {m : Nat} (hm : m ≤ w.length) :
    prefixOf (w.push c) m = prefixOf w m := by
  apply String.ext
  have hm' : m ≤ w.toList.length := by
    simpa [String.length_toList] using hm
  have htake : (w.toList ++ [c]).take m = w.toList.take m := by
    simpa using
      (List.take_append_of_le_length (l₁ := w.toList) (l₂ := [c]) (i := m) hm')
  simpa [prefixOf, String.toList_push] using htake

lemma suffixFrom_push_of_le (w : String) (c : Char) {k : Nat} (hk : k ≤ w.length) :
    suffixFrom (w.push c) k = (suffixFrom w k).push c := by
  apply String.ext
  have hk' : k ≤ w.toList.length := by
    simpa [String.length_toList] using hk
  have hdrop : (w.toList ++ [c]).drop k = w.toList.drop k ++ [c] := by
    simpa using
      (List.drop_append_of_le_length (l₁ := w.toList) (l₂ := [c]) (i := k) hk')
  simpa [suffixFrom, String.toList_push] using hdrop

lemma prefixOf_self (w : String) : prefixOf w w.length = w := by
  apply String.ext
  simp [prefixOf, String.length_toList]

lemma suffixFrom_self (w : String) : suffixFrom w w.length = "" := by
  apply String.ext
  simp [suffixFrom, String.length_toList]

lemma prefixOf_of_mem_extensions {w s : String} {m : Nat}
    (hs : s ∈ K5Data.extensions w) (hm : m ≤ w.length) :
    prefixOf s m = prefixOf w m := by
  rcases mem_extensions (w := w) (s := s) hs with rfl | rfl
  · exact prefixOf_push_of_le (w := w) (c := '0') hm
  · exact prefixOf_push_of_le (w := w) (c := '1') hm

lemma suffixFrom_of_mem_extensions {w s : String} {k : Nat}
    (hs : s ∈ K5Data.extensions w) (hk : k ≤ w.length) :
    ∃ c : Char, suffixFrom s k = (suffixFrom w k).push c := by
  rcases mem_extensions (w := w) (s := s) hs with rfl | rfl
  · exact ⟨'0', suffixFrom_push_of_le (w := w) (c := '0') hk⟩
  · exact ⟨'1', suffixFrom_push_of_le (w := w) (c := '1') hk⟩

lemma filter_prefix_exact {m : Nat} {x : String} (hx : x ∈ allowedWordsFinset m) :
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

lemma filter_pref_suf_empty {m L : Nat} {x : String} (hL : L = m + 5) :
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

lemma filter_prefix_step {m n : Nat} {x : String} (hm : m ≤ n + 1) :
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

lemma filter_pref_suf_step {m n : Nat} {x u : String} {c : Char}
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

end Step2Sparse

end Model

end K5Bridge

end FiniteDependence.MIS
