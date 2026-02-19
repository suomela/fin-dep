import FiniteDependence.Coloring.InsertDeletion
import Mathlib.Data.Nat.Choose.Basic

/-!
# Proposition 11, case `q = 4`

This file proves the `q = 4` case of Proposition 11 in Holroyd–Liggett (arXiv:1403.2448v4).
-/

open scoped BigOperators

namespace FiniteDependence.Coloring

namespace Word

open Nat

private def emptyWord : Word 4 0 := fun i : Fin 0 => i.elim0

private lemma insert1_empty_left {n : ℕ} (a : Fin 4) (y : Word 4 n) :
    insert1 (q := 4) (m := 0) (n := n) emptyWord a y
      = Word.cast (q := 4) (Nat.add_comm n 1) (cons a y) := by
  classical
  funext i
  have h :=
    (Fin.append_left_eq_cons (x₀ := snoc (q := 4) (n := 0) emptyWord a) (x := y))
  have hi := congrArg (fun f => f i) h
  simpa [Word.insert1, Word.append, Word.snoc, Word.cons, Word.cast, emptyWord, Function.comp] using hi

private lemma insert1_empty_right {m : ℕ} (x : Word 4 m) (a : Fin 4) :
    insert1 (q := 4) (m := m) (n := 0) x a emptyWord = snoc x a := by
  classical
  funext i
  have hempty : (emptyWord : Fin 0 → Fin 4) = Fin.elim0 := rfl
  have h := congrArg (fun f => f i) (Fin.append_elim0 (u := snoc x a))
  have hcast : (Fin.cast (Nat.add_zero (m + 1)) i) = i := by
    apply Fin.ext
    simp
  -- Avoid `simp` rewriting the goal to `True`; finish by rewriting explicitly.
  dsimp [Word.insert1, Word.append] at *
  simp [hempty, Function.comp]

private lemma sum_univ_eq_sum_erase {β : Type*} [AddCommMonoid β] [DecidableEq (Fin 4)]
    (a : Fin 4) (f : Fin 4 → β) (hfa : f a = 0) :
    (∑ x : Fin 4, f x) = ∑ x ∈ (Finset.univ.erase a), f x := by
  have h :=
    (Finset.sum_erase_add (s := (Finset.univ : Finset (Fin 4))) (a := a) (f := f)
      (Finset.mem_univ a)).symm
  simpa [hfa] using h

private lemma sum_univ_eq_sum_erase_erase {β : Type*} [AddCommMonoid β] [DecidableEq (Fin 4)]
    (a b : Fin 4) (hab : b ≠ a) (f : Fin 4 → β) (hfa : f a = 0) (hfb : f b = 0) :
    (∑ x : Fin 4, f x) = ∑ x ∈ ((Finset.univ.erase a).erase b), f x := by
  have hb_mem : b ∈ (Finset.univ.erase a) := by
    simp [Finset.mem_erase, hab]
  have h1 := sum_univ_eq_sum_erase (a := a) (f := f) hfa
  have h2 :=
    (Finset.sum_erase_add (s := (Finset.univ.erase a)) (a := b) (f := f) hb_mem).symm
  -- Combine `h1` and `h2`.
  calc
    (∑ x : Fin 4, f x)
        = (∑ x ∈ (Finset.univ.erase a), f x) := h1
    _ = (∑ x ∈ ((Finset.univ.erase a).erase b), f x) + f b := by
          simpa using h2
    _ = ∑ x ∈ ((Finset.univ.erase a).erase b), f x := by simp [hfb]

private lemma B_insert1_eq_zero_of_eq_last {m n : ℕ} (x : Word 4 (m + 1)) (y : Word 4 (n + 1)) :
    B (insert1 x (x (Fin.last m)) y) = 0 := by
  have hsnoc : ¬ IsProper (snoc x (x (Fin.last m))) := Word.not_isProper_snoc_self (x := x)
  have hnot : ¬ IsProper (insert1 x (x (Fin.last m)) y) := by
    simpa [Word.insert1] using
      (Word.not_isProper_append_left_of_not_isProper (q := 4) (x := snoc x (x (Fin.last m))) (y := y) hsnoc)
  -- `insert1 x _ y` has length `(m+1)+1+(n+1) = (m+2+n)+1`.
  simpa using (B_eq_zero_of_not_isProper (q := 4) (x := insert1 x (x (Fin.last m)) y) (n := m + 2 + n) hnot)

private lemma B_insert1_eq_zero_of_eq_first {m n : ℕ} (x : Word 4 m) (y : Word 4 (n + 1)) :
    B (insert1 x (y 0) y) = 0 := by
  have hbd : (snoc x (y 0)) (Fin.last m) = y 0 := by
    -- last letter of a `snoc` is the appended one
    simp [Word.snoc]
  have hnot : ¬ IsProper (insert1 x (y 0) y) := by
    -- boundary failure in the append
    have : ¬ IsProper (append (snoc x (y 0)) y) :=
      Word.not_isProper_append_of_eq_boundary (q := 4) (x := snoc x (y 0)) (y := y) hbd
    simpa [Word.insert1] using this
  -- `insert1 x _ y` has length `m + 1 + (n + 1) = (m + n + 1) + 1`.
  have hlen : m + 1 + (n + 1) = (m + n + 1) + 1 := by
    ac_rfl
  have hnot' : ¬ IsProper (Word.cast (q := 4) hlen (insert1 x (y 0) y)) := by
    simpa [Word.isProper_cast_iff] using hnot
  have hB0 :
      B (Word.cast (q := 4) hlen (insert1 x (y 0) y)) = 0 := by
    simpa using
      (B_eq_zero_of_not_isProper (q := 4)
        (x := Word.cast (q := 4) hlen (insert1 x (y 0) y)) (n := m + n + 1) hnot')
  simpa [B_cast] using hB0

private lemma insert1_erase_last_eq_append {m n : ℕ} (x : Word 4 (m + 1)) (y : Word 4 (n + 1)) :
    insert1 (erase (n := m) x (Fin.last m)) (x (Fin.last m)) y = append x y := by
  have hx : snoc (erase (n := m) x (Fin.last m)) (x (Fin.last m)) = x := by
    simp
  -- Rewriting `snoc (erase ...) (x last)` to `x` makes the claim definitional.
  simp [Word.insert1, Word.append, hx]

private lemma B_insert1_erase_last_eq_B_append {m n : ℕ} (x : Word 4 (m + 1)) (y : Word 4 (n + 1)) :
    B (insert1 (erase (n := m) x (Fin.last m)) (x (Fin.last m)) y) = B (append x y) := by
  simp [insert1_erase_last_eq_append (x := x) (y := y)]

private lemma cons_erase_zero {n : ℕ} (y : Word 4 (n + 1)) :
    cons (y 0) (erase (n := n) y 0) = y := by
  classical
  funext i
  induction i using Fin.cases with
  | zero =>
      simp [Word.cons]
  | succ i =>
      -- `erase y 0 i = y i.succ` since `succAbove 0 = succ`.
      simp [Word.cons, Word.erase]

private lemma append_eq_cast_insert1_erase_zero {m n : ℕ} (x : Word 4 (m + 1)) (y : Word 4 (n + 1)) :
    append x y =
      Word.cast (q := 4) (Nat.succ_add_eq_add_succ (m + 1) n)
        (insert1 x (y 0) (erase (n := n) y 0)) := by
  classical
  have hy : cons (y 0) (erase (n := n) y 0) = y := cons_erase_zero (y := y)
  -- Start from `Fin.append_right_cons` and rewrite the `cons` term to `y`.
  have h := Fin.append_right_cons (xs := x) (y := y 0) (ys := erase (n := n) y 0)
  have h' :
      append x y
        = (append (snoc x (y 0)) (erase (n := n) y 0))
            ∘ Fin.cast (Nat.succ_add_eq_add_succ (m + 1) n).symm := by
    have h1 :
        append x (cons (y 0) (erase (n := n) y 0))
          = append (snoc x (y 0)) (erase (n := n) y 0)
              ∘ Fin.cast (Nat.succ_add_eq_add_succ (m + 1) n).symm := by
      simpa [Word.append, Word.snoc, Word.cons] using h
    simpa [hy] using h1
  funext i
  have hi := congrArg (fun f => f i) h'
  simpa [Word.insert1, Word.append, Word.cast, Function.comp] using hi

private lemma B_append_eq_B_insert1_erase_zero {m n : ℕ} (x : Word 4 (m + 1)) (y : Word 4 (n + 1)) :
    B (append x y) = B (insert1 x (y 0) (erase (n := n) y 0)) := by
  -- Use the cast relation and invariance of `B` under casts.
  have h := congrArg (fun z => B (q := 4) z) (append_eq_cast_insert1_erase_zero (m := m) (n := n) x y)
  -- `B_cast` removes the cast on the RHS.
  simpa [B_cast] using h

/-- Proposition 11 (q=4): summing `B` over the inserted letter. -/
theorem sum_B_insert1_four :
    ∀ {m n : ℕ} (x : Word 4 m) (y : Word 4 n),
      (∑ a : Fin 4, B (insert1 x a y))
        = 2 * choose (m + n + 2) (m + 1) * B x * B y := by
  classical
  intro m n x y
  -- Induction on `k = m + n`.
  have hk :
      ∀ k : ℕ, ∀ {m n : ℕ} (x : Word 4 m) (y : Word 4 n),
        m + n = k →
          (∑ a : Fin 4, B (insert1 x a y))
            = 2 * choose (m + n + 2) (m + 1) * B x * B y := by
    intro k
    induction k with
    | zero =>
        intro m n x y hmn
        have hm : m = 0 := Nat.eq_zero_of_add_eq_zero_right hmn
        have hn : n = 0 := Nat.eq_zero_of_add_eq_zero_left hmn
        subst hm; subst hn
        have hx0 : x = emptyWord := Subsingleton.elim _ _
        have hy0 : y = emptyWord := Subsingleton.elim _ _
        subst hx0; subst hy0
        -- `B` is `1` on words of length `1`, so the sum over `Fin 4` is `4`.
        simp [Word.B, Word.IsProper]
    | succ k ih =>
        intro m n x y hmn
        cases m with
        | zero =>
            -- Reduce to Proposition 10 (left-end version).
            have hx0 : x = emptyWord := Subsingleton.elim _ _
            subst hx0
            calc
              (∑ a : Fin 4, B (insert1 (q := 4) (m := 0) (n := n) emptyWord a y))
                  = ∑ a : Fin 4, B (cons a y) := by
                      refine Fintype.sum_congr _ _ ?_
                      intro a
                      simp [insert1_empty_left, B_cast]
              _ = (n * (4 - 2) + 4) * B y := by
                      simpa using (sum_B_cons (q := 4) (by decide : 2 ≤ (4 : ℕ)) (x := y))
              _ = 2 * choose (0 + n + 2) (0 + 1) * B (q := 4) emptyWord * B y := by
                      simp [Nat.choose_one_right, Nat.mul_assoc, Nat.mul_comm, Nat.mul_add, Nat.add_mul]
        | succ m =>
            cases n with
            | zero =>
                -- Reduce to Proposition 10 (right-end version).
                have hy0 : y = emptyWord := Subsingleton.elim _ _
                subst hy0
                calc
                  (∑ a : Fin 4, B (insert1 x a emptyWord))
                      = ∑ a : Fin 4, B (snoc x a) := by
                          refine Fintype.sum_congr _ _ ?_
                          intro a
                          simp [insert1_empty_right]
                  _ = ((m + 1) * (4 - 2) + 4) * B x := by
                          simpa using (sum_B_snoc (q := 4) (by decide : 2 ≤ (4 : ℕ)) (x := x))
                  _ = 2 * choose ((m + 1) + 0 + 2) ((m + 1) + 1) * B x * B (q := 4) emptyWord := by
                          simp [Nat.choose_succ_self_right, Nat.mul_assoc, Nat.mul_comm, Nat.add_assoc, Nat.mul_add, Nat.add_mul]
            | succ n =>
                -- Main case: both sides nonempty.
                by_cases hx : IsProper x
                · by_cases hy : IsProper y
                  · -- Proper case: split on boundary colors.
                    let xm : Fin 4 := x (Fin.last m)
                    let y1 : Fin 4 := y 0
                    let xy : Word 4 ((m + 1) + (n + 1)) := append x y

                    have hkx : m + (n + 1) = k := by
                      -- Cancel `+ 1` from the right.
                      have h₁ : m + 1 + (n + 1) = m + (n + 1) + 1 := by
                        ac_rfl
                      have h' : (m + (n + 1)) + 1 = k + 1 := h₁.symm.trans hmn
                      exact Nat.add_right_cancel h'
                    have hky : (m + 1) + n = k := by
                      have h₁ : m + 1 + (n + 1) = (m + 1) + n + 1 := by
                        ac_rfl
                      have h' : ((m + 1) + n) + 1 = k + 1 := h₁.symm.trans hmn
                      exact Nat.add_right_cancel h'

                    have hxB : B x = ∑ i : Fin (m + 1), B (erase (n := m) x i) := by
                      simpa using (B_eq_sum_erase_of_isProper (q := 4) (x := x) (n := m) hx)
                    have hyB : B y = ∑ j : Fin (n + 1), B (erase (n := n) y j) := by
                      simpa using (B_eq_sum_erase_of_isProper (q := 4) (x := y) (n := n) hy)

                    by_cases hxy : xm = y1
                    · -- Case `xm = y1` (equation (3) in the paper).
                      let allowSet : Finset (Fin 4) := Finset.univ.erase xm

                      have hxyB : B xy = 0 := by
                        have hnot : ¬ IsProper xy := by
                          have : x (Fin.last m) = y 0 := by simpa [xm, y1] using hxy
                          simpa [xy] using
                            (Word.not_isProper_append_of_eq_boundary (q := 4) (x := x) (y := y) this)
                        simpa [xy] using
                          (B_eq_zero_of_not_isProper (q := 4) (x := xy) (n := (m + 1) + n) hnot)

                      have h_forbidden : B (insert1 x xm y) = 0 := by
                        simpa [xm] using B_insert1_eq_zero_of_eq_last (m := m) (n := n) (x := x) (y := y)

                      have h_sum :
                          (∑ a : Fin 4, B (insert1 x a y))
                            = ∑ a ∈ allowSet, B (insert1 x a y) := by
                        simpa [allowSet] using
                          (sum_univ_eq_sum_erase (a := xm) (f := fun a => B (insert1 x a y)) h_forbidden)

                      have h_proper (a : Fin 4) (ha : a ∈ allowSet) :
                            IsProper (insert1 x a y) := by
                          have ha_ne : a ≠ xm := (Finset.mem_erase.mp ha).1
                          have hxsnoc : IsProper (snoc x a) :=
                            (Word.isProper_snoc_iff (x := x) (a := a)).2 ⟨hx, by simpa [xm] using ha_ne.symm⟩
                          have hbd : (snoc x a) (Fin.last (m + 1)) ≠ y 0 := by
                            -- last letter of `snoc x a` is `a`, and `y 0 = xm`.
                            simpa [Word.snoc, xm, y1, hxy] using ha_ne
                          simpa [Word.insert1] using
                            (Word.isProper_append_of_isProper (q := 4) (x := snoc x a) (y := y) hxsnoc hy hbd)

                      have h_expand (a : Fin 4) (ha : a ∈ allowSet) :
                          B (insert1 x a y)
                            = (∑ i : Fin (m + 1), B (insert1 (erase (n := m) x i) a y))
                              + B xy
                              + ∑ j : Fin (n + 1), B (insert1 x a (erase (n := n) y j)) := by
                        have := B_insert1_eq (q := 4) (m := m) (n := n) (x := x) (a := a) (y := y)
                          (hxy := h_proper a ha)
                        simpa [xy, add_assoc] using this

                      -- Evaluate `i`-inner sums by IH (missing `xm` is always 0 since `xm = y1`).
                      have hx_sum (i : Fin (m + 1)) :
                            (∑ a ∈ allowSet, B (insert1 (erase (n := m) x i) a y))
                              = 2 * choose (m + n + 3) (m + 1) * B (erase (n := m) x i) * B y := by
                          have h_missing : B (insert1 (erase (n := m) x i) xm y) = 0 := by
                            -- Boundary failure: inserted `xm = y1` equals the first of `y`.
                            have hnot : ¬ IsProper (insert1 (erase (n := m) x i) xm y) := by
                              have hbd : (snoc (erase (n := m) x i) xm) (Fin.last m) = y 0 := by
                                simp [Word.snoc, xm, y1, hxy]
                              have : ¬ IsProper (append (snoc (erase (n := m) x i) xm) y) :=
                                Word.not_isProper_append_of_eq_boundary (q := 4)
                                  (x := snoc (erase (n := m) x i) xm) (y := y) hbd
                              simpa [Word.insert1] using this
                            -- Length is `m + 1 + (n + 1)`.
                            simpa [Nat.add_assoc] using
                              (B_eq_zero_of_not_isProper (q := 4)
                                (x := insert1 (q := 4) (m := m) (n := n + 1) (erase (n := m) x i) xm y)
                                (n := (m + 1) + n) hnot)
                          have hfull :
                              (∑ a : Fin 4, B (insert1 (erase (n := m) x i) a y))
                                = ∑ a ∈ allowSet, B (insert1 (erase (n := m) x i) a y) := by
                            simpa [allowSet] using
                              (sum_univ_eq_sum_erase (a := xm) (f := fun a => B (insert1 (erase (n := m) x i) a y)) h_missing)
                          have hih :=
                            ih (m := m) (n := n + 1) (x := erase (n := m) x i) (y := y) hkx
                          calc
                            (∑ a ∈ allowSet, B (insert1 (erase (n := m) x i) a y))
                                = ∑ a : Fin 4, B (insert1 (erase (n := m) x i) a y) := by
                                    simpa using hfull.symm
                            _ = 2 * choose (m + (n + 1) + 2) (m + 1) * B (erase (n := m) x i) * B y := by
                                    simpa using hih
                            _ = 2 * choose (m + n + 3) (m + 1) * B (erase (n := m) x i) * B y := by
                                    simp [Nat.add_assoc]

                      -- Evaluate `j`-inner sums by IH (missing `xm` is 0 since it repeats the last letter of `x`).
                      have hy_sum (j : Fin (n + 1)) :
                            (∑ a ∈ allowSet, B (insert1 x a (erase (n := n) y j)))
                              = 2 * choose (m + n + 3) (m + 2) * B x * B (erase (n := n) y j) := by
                          have h_missing : B (insert1 x xm (erase (n := n) y j)) = 0 := by
                            -- Repeats the last letter of `x`, so never proper.
                            have hsnoc : ¬ IsProper (snoc x xm) := by
                              simpa [xm] using (Word.not_isProper_snoc_self (x := x))
                            have hnot : ¬ IsProper (insert1 x xm (erase (n := n) y j)) := by
                              cases n with
                              | zero =>
                                  -- Right part is empty, so this is just `snoc x xm`.
                                  have hy0 : erase (n := 0) y j = emptyWord := Subsingleton.elim _ _
                                  simpa [hy0, insert1_empty_right] using hsnoc
                              | succ n =>
                                  have : ¬ IsProper (append (snoc x xm) (erase (n := Nat.succ n) y j)) :=
                                    Word.not_isProper_append_left_of_not_isProper (q := 4)
                                      (x := snoc x xm) (y := erase (n := Nat.succ n) y j) hsnoc
                                  simpa [Word.insert1] using this
                            -- Cast the length into the syntactic form `((m + 1) + n) + 1` required by
                            -- `B_eq_zero_of_not_isProper`.
                            have hlen : (m + 1) + 1 + n = (m + 1) + n + 1 := by
                              ac_rfl
                            have hnot' :
                                ¬ IsProper
                                  (Word.cast (q := 4) hlen
                                    (insert1 (q := 4) (m := m + 1) (n := n) x xm (erase (n := n) y j))) := by
                              simpa [Word.isProper_cast_iff] using hnot
                            have hcast :
                                B
                                    (Word.cast (q := 4) hlen
                                      (insert1 (q := 4) (m := m + 1) (n := n) x xm (erase (n := n) y j))) =
                                  0 := by
                              simpa using
                                (B_eq_zero_of_not_isProper (q := 4)
                                  (x :=
                                    Word.cast (q := 4) hlen
                                      (insert1 (q := 4) (m := m + 1) (n := n) x xm (erase (n := n) y j)))
                                  (n := (m + 1) + n) hnot')
                            simpa [B_cast] using hcast
                          have hfull :
                              (∑ a : Fin 4, B (insert1 x a (erase (n := n) y j)))
                                = ∑ a ∈ allowSet, B (insert1 x a (erase (n := n) y j)) := by
                            simpa [allowSet] using
                              (sum_univ_eq_sum_erase (a := xm) (f := fun a => B (insert1 x a (erase (n := n) y j))) h_missing)
                          have hih :=
                            ih (m := m + 1) (n := n) (x := x) (y := erase (n := n) y j) hky
                          calc
                            (∑ a ∈ allowSet, B (insert1 x a (erase (n := n) y j)))
                                = ∑ a : Fin 4, B (insert1 x a (erase (n := n) y j)) := by
                                    simpa using hfull.symm
                            _ = 2 * choose ((m + 1) + n + 2) ((m + 1) + 1) * B x * B (erase (n := n) y j) := by
                                    simpa using hih
                            _ = 2 * choose (m + n + 3) (m + 2) * B x * B (erase (n := n) y j) := by
                                    -- Only rewrite the binomial-coefficient arguments.
                                    have h₁ : (m + 1) + n + 2 = m + n + 3 := by
                                      ac_rfl
                                    have h₂ : (m + 1) + 1 = m + 2 := by
                                      simp [Nat.add_assoc]
                                    simp [h₁, h₂]

                      -- Sum the expansion over `allowSet`.
                      have h_allow :
                          (∑ a ∈ allowSet, B (insert1 x a y))
                            = 2 * (choose (m + n + 3) (m + 1) + choose (m + n + 3) (m + 2)) * B x * B y := by
                        calc
                          (∑ a ∈ allowSet, B (insert1 x a y))
                              = ∑ a ∈ allowSet,
                                  ((∑ i : Fin (m + 1), B (insert1 (erase (n := m) x i) a y))
                                    + B xy
                                    + ∑ j : Fin (n + 1), B (insert1 x a (erase (n := n) y j))) := by
                                  refine Finset.sum_congr rfl ?_
                                  intro a ha
                                  simp [h_expand a ha]
                          _ = (∑ i : Fin (m + 1), ∑ a ∈ allowSet, B (insert1 (erase (n := m) x i) a y))
                                + (∑ a ∈ allowSet, B xy)
                                + ∑ j : Fin (n + 1), ∑ a ∈ allowSet, B (insert1 x a (erase (n := n) y j)) := by
                                  -- Distribute sums over `allowSet`, then swap the order in the double sums.
                                  have hdistrib :
                                      (∑ a ∈ allowSet,
                                          ((∑ i : Fin (m + 1), B (insert1 (erase (n := m) x i) a y))
                                            + B xy
                                            + ∑ j : Fin (n + 1), B (insert1 x a (erase (n := n) y j))))
                                        = (∑ a ∈ allowSet, ∑ i : Fin (m + 1), B (insert1 (erase (n := m) x i) a y))
                                            + (∑ a ∈ allowSet, B xy)
                                            + (∑ a ∈ allowSet, ∑ j : Fin (n + 1), B (insert1 x a (erase (n := n) y j))) := by
                                    -- Two applications of `Finset.sum_add_distrib`.
                                    calc
                                      (∑ a ∈ allowSet,
                                            ((∑ i : Fin (m + 1), B (insert1 (erase (n := m) x i) a y))
                                              + B xy
                                              + ∑ j : Fin (n + 1), B (insert1 x a (erase (n := n) y j))))
                                          = ∑ a ∈ allowSet,
                                              ((∑ i : Fin (m + 1), B (insert1 (erase (n := m) x i) a y))
                                                + (B xy + ∑ j : Fin (n + 1), B (insert1 x a (erase (n := n) y j)))) := by
                                                refine Finset.sum_congr rfl ?_
                                                intro a ha
                                                ac_rfl
                                      _ = (∑ a ∈ allowSet, (∑ i : Fin (m + 1), B (insert1 (erase (n := m) x i) a y)))
                                            + ∑ a ∈ allowSet, (B xy + ∑ j : Fin (n + 1), B (insert1 x a (erase (n := n) y j))) := by
                                                simp [Finset.sum_add_distrib]
                                      _ = (∑ a ∈ allowSet, (∑ i : Fin (m + 1), B (insert1 (erase (n := m) x i) a y)))
                                            + ((∑ a ∈ allowSet, B xy)
                                                + (∑ a ∈ allowSet, ∑ j : Fin (n + 1), B (insert1 x a (erase (n := n) y j)))) := by
                                                simp [Finset.sum_add_distrib]
                                      _ = _ := by
                                                ac_rfl

                                  have hswap_left :
                                      (∑ a ∈ allowSet, ∑ i : Fin (m + 1), B (insert1 (erase (n := m) x i) a y))
                                        = ∑ i : Fin (m + 1), ∑ a ∈ allowSet, B (insert1 (erase (n := m) x i) a y) := by
                                    -- `Finset.sum_comm` swaps the two finite sums.
                                    simpa using
                                      (Finset.sum_comm (s := allowSet) (t := (Finset.univ : Finset (Fin (m + 1))))
                                        (f := fun a i => B (insert1 (erase (n := m) x i) a y)))

                                  have hswap_right :
                                      (∑ a ∈ allowSet, ∑ j : Fin (n + 1), B (insert1 x a (erase (n := n) y j)))
                                        = ∑ j : Fin (n + 1), ∑ a ∈ allowSet, B (insert1 x a (erase (n := n) y j)) := by
                                    simpa using
                                      (Finset.sum_comm (s := allowSet) (t := (Finset.univ : Finset (Fin (n + 1))))
                                        (f := fun a j => B (insert1 x a (erase (n := n) y j))) )

                                  -- Put everything together.
                                  calc
                                    (∑ a ∈ allowSet,
                                          ((∑ i : Fin (m + 1), B (insert1 (erase (n := m) x i) a y))
                                            + B xy
                                            + ∑ j : Fin (n + 1), B (insert1 x a (erase (n := n) y j))))
                                        = (∑ a ∈ allowSet, ∑ i : Fin (m + 1), B (insert1 (erase (n := m) x i) a y))
                                            + (∑ a ∈ allowSet, B xy)
                                            + (∑ a ∈ allowSet, ∑ j : Fin (n + 1), B (insert1 x a (erase (n := n) y j))) := by
                                            simpa using hdistrib
                                    _ = (∑ i : Fin (m + 1), ∑ a ∈ allowSet, B (insert1 (erase (n := m) x i) a y))
                                          + (∑ a ∈ allowSet, B xy)
                                          + (∑ j : Fin (n + 1), ∑ a ∈ allowSet, B (insert1 x a (erase (n := n) y j))) := by
                                            -- Rewrite both double sums using the swap lemmas.
                                            -- Be explicit to avoid `simp` loops.
                                            rw [hswap_left, hswap_right]
                          _ = (∑ i : Fin (m + 1), 2 * choose (m + n + 3) (m + 1) * B (erase (n := m) x i) * B y)
                                + (allowSet.card * B xy)
                                + ∑ j : Fin (n + 1),
                                    2 * choose (m + n + 3) (m + 2) * B x * B (erase (n := n) y j) := by
                                  -- Substitute `hx_sum` and `hy_sum`.
                                  have h1 :
                                      (∑ i : Fin (m + 1), ∑ a ∈ allowSet, B (insert1 (erase (n := m) x i) a y))
                                        = ∑ i : Fin (m + 1), 2 * choose (m + n + 3) (m + 1) * B (erase (n := m) x i) * B y := by
                                      refine Fintype.sum_congr _ _ ?_
                                      intro i
                                      exact hx_sum i
                                  have h2 :
                                      (∑ j : Fin (n + 1), ∑ a ∈ allowSet, B (insert1 x a (erase (n := n) y j)))
                                        = ∑ j : Fin (n + 1),
                                            2 * choose (m + n + 3) (m + 2) * B x * B (erase (n := n) y j) := by
                                      refine Fintype.sum_congr _ _ ?_
                                      intro j
                                      exact hy_sum j
                                  have hmid : (∑ a ∈ allowSet, B xy) = allowSet.card * B xy := by
                                    simp
                                  simp [h1, h2, hmid, add_assoc]
                          _ = 2 * choose (m + n + 3) (m + 1) * B x * B y
                                + (allowSet.card * B xy)
                                + 2 * choose (m + n + 3) (m + 2) * B x * B y := by
                                  -- Evaluate each of the two outer sums using `hxB` and `hyB`.
                                  have hx_total :
                                      (∑ i : Fin (m + 1),
                                          2 * choose (m + n + 3) (m + 1) * B (erase (n := m) x i) * B y)
                                        = 2 * choose (m + n + 3) (m + 1) * B x * B y := by
                                    -- Factor out the constant `2 * choose ... * B y` and use `hxB`.
                                    have hmul :
                                        (∑ i : Fin (m + 1),
                                            (2 * choose (m + n + 3) (m + 1) * B y) * B (erase (n := m) x i))
                                          = (2 * choose (m + n + 3) (m + 1) * B y)
                                              * (∑ i : Fin (m + 1), B (erase (n := m) x i)) := by
                                      simpa using
                                        (Finset.mul_sum (s := (Finset.univ : Finset (Fin (m + 1))))
                                          (f := fun i : Fin (m + 1) => B (erase (n := m) x i))
                                          (a := 2 * choose (m + n + 3) (m + 1) * B y)).symm
                                    calc
                                      (∑ i : Fin (m + 1),
                                            2 * choose (m + n + 3) (m + 1) * B (erase (n := m) x i) * B y)
                                          = ∑ i : Fin (m + 1),
                                              (2 * choose (m + n + 3) (m + 1) * B y)
                                                * B (erase (n := m) x i) := by
                                                refine Fintype.sum_congr _ _ ?_
                                                intro i
                                                ac_rfl
                                      _ = (2 * choose (m + n + 3) (m + 1) * B y)
                                            * (∑ i : Fin (m + 1), B (erase (n := m) x i)) := hmul
                                      _ = (2 * choose (m + n + 3) (m + 1) * B y) * B x := by
                                            simpa using congrArg (fun t => (2 * choose (m + n + 3) (m + 1) * B y) * t) hxB.symm
                                      _ = 2 * choose (m + n + 3) (m + 1) * B x * B y := by
                                            ac_rfl

                                  have hy_total :
                                      (∑ j : Fin (n + 1),
                                          2 * choose (m + n + 3) (m + 2) * B x * B (erase (n := n) y j))
                                        = 2 * choose (m + n + 3) (m + 2) * B x * B y := by
                                    -- Factor out the constant `2 * choose ... * B x` and use `hyB`.
                                    have hmul :
                                        (∑ j : Fin (n + 1),
                                            (2 * choose (m + n + 3) (m + 2) * B x) * B (erase (n := n) y j))
                                          = (2 * choose (m + n + 3) (m + 2) * B x)
                                              * (∑ j : Fin (n + 1), B (erase (n := n) y j)) := by
                                      simpa using
                                        (Finset.mul_sum (s := (Finset.univ : Finset (Fin (n + 1))))
                                          (f := fun j : Fin (n + 1) => B (erase (n := n) y j))
                                          (a := 2 * choose (m + n + 3) (m + 2) * B x)).symm
                                    calc
                                      (∑ j : Fin (n + 1),
                                            2 * choose (m + n + 3) (m + 2) * B x * B (erase (n := n) y j))
                                          = ∑ j : Fin (n + 1),
                                              (2 * choose (m + n + 3) (m + 2) * B x)
                                                * B (erase (n := n) y j) := by
                                                refine Fintype.sum_congr _ _ ?_
                                                intro j
                                                ac_rfl
                                      _ = (2 * choose (m + n + 3) (m + 2) * B x)
                                            * (∑ j : Fin (n + 1), B (erase (n := n) y j)) := hmul
                                      _ = (2 * choose (m + n + 3) (m + 2) * B x) * B y := by
                                            simpa using congrArg (fun t => (2 * choose (m + n + 3) (m + 2) * B x) * t) hyB.symm
                                      _ = 2 * choose (m + n + 3) (m + 2) * B x * B y := by
                                            ac_rfl

                                  -- Substitute the evaluated sums.
                                  rw [hx_total, hy_total]
                          _ = 2 * (choose (m + n + 3) (m + 1) + choose (m + n + 3) (m + 2)) * B x * B y := by
                                  -- Middle term vanishes because `B xy = 0`.
                                  have : allowSet.card * B xy = 0 := by simp [allowSet, hxyB]
                                  simp [this, Nat.mul_add, Nat.add_mul, Nat.mul_assoc, add_assoc, add_comm]

                      have hpascal :
                          choose (m + n + 4) (m + 2) = choose (m + n + 3) (m + 1) + choose (m + n + 3) (m + 2) := by
                        simpa [Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using
                          (Nat.choose_succ_succ' (n := m + n + 3) (k := m + 1))

                      calc
                        (∑ a : Fin 4, B (insert1 x a y))
                            = ∑ a ∈ allowSet, B (insert1 x a y) := h_sum
                        _ = 2 * (choose (m + n + 3) (m + 1) + choose (m + n + 3) (m + 2)) * B x * B y := h_allow
                        _ = 2 * choose (m + n + 4) (m + 2) * B x * B y := by
                              simp [hpascal, Nat.mul_assoc]

                      -- Rewrite the binomial coefficient arguments to match the statement.
                      have hchoose :
                          2 * choose (m + n + 4) (m + 2) * B x * B y
                            = 2 * choose ((m + 1) + (n + 1) + 2) ((m + 1) + 1) * B x * B y := by
                        have h₁ : m + n + 4 = (m + 1) + (n + 1) + 2 := by
                          ac_rfl
                        have h₂ : m + 2 = (m + 1) + 1 := by
                          simp [Nat.add_assoc]
                        -- Only rewrite the arguments of `choose`.
                        simp [h₁, h₂]

                      -- Use the normalization rewrite.
                      simp [hchoose]

                    · -- Case `xm ≠ y1` (equation (5) in the paper).
                      let allowSet : Finset (Fin 4) := (Finset.univ.erase xm).erase y1
                      have hcard : allowSet.card = 2 := by
                        have hy_mem : y1 ∈ (Finset.univ.erase xm) := by
                          simp [Finset.mem_erase, (ne_comm).1 hxy]
                        have hcard1 : (Finset.univ.erase xm).card = 3 := by
                          simp
                        have hcard2 : allowSet.card = (Finset.univ.erase xm).card - 1 := by
                          simpa [allowSet] using
                            (Finset.card_erase_of_mem (s := (Finset.univ.erase xm)) hy_mem)
                        simpa [hcard1] using hcard2

                      have h_forbidden_xm : B (insert1 x xm y) = 0 := by
                        simpa [xm] using
                          B_insert1_eq_zero_of_eq_last (m := m) (n := n) (x := x) (y := y)

                      have h_forbidden_y1 : B (insert1 x y1 y) = 0 := by
                        -- Boundary failure with the first symbol of `y`.
                        simpa [y1] using
                          B_insert1_eq_zero_of_eq_first (x := x) (y := y)

                      have h_sum :
                          (∑ a : Fin 4, B (insert1 x a y))
                            = ∑ a ∈ allowSet, B (insert1 x a y) := by
                        have hab : y1 ≠ xm := (ne_comm).1 hxy
                        simpa [allowSet] using
                          (sum_univ_eq_sum_erase_erase (a := xm) (b := y1) (hab := hab)
                            (f := fun a => B (insert1 x a y)) (hfa := h_forbidden_xm)
                            (hfb := h_forbidden_y1))

                      have h_proper (a : Fin 4) (ha : a ∈ allowSet) :
                          IsProper (insert1 x a y) := by
                        have ha' : a ≠ y1 ∧ a ≠ xm := by
                          -- Membership in the doubly-erased set gives both inequalities.
                          simpa [allowSet] using ha
                        have ha_ne_y1 : a ≠ y1 := ha'.1
                        have ha_ne_xm : a ≠ xm := ha'.2
                        have hxsnoc : IsProper (snoc x a) :=
                          (Word.isProper_snoc_iff (x := x) (a := a)).2 ⟨hx, by
                            -- `x (last m) = xm`.
                            simpa [xm] using ha_ne_xm.symm⟩
                        have hbd : (snoc x a) (Fin.last (m + 1)) ≠ y 0 := by
                          -- last letter of `snoc x a` is `a`.
                          simpa [y1] using ha_ne_y1
                        simpa [Word.insert1] using
                          (Word.isProper_append_of_isProper (q := 4) (x := snoc x a) (y := y) hxsnoc hy hbd)

                      have h_expand (a : Fin 4) (ha : a ∈ allowSet) :
                          B (insert1 x a y)
                            = (∑ i : Fin (m + 1), B (insert1 (erase (n := m) x i) a y))
                              + B xy
                              + ∑ j : Fin (n + 1), B (insert1 x a (erase (n := n) y j)) := by
                        have := B_insert1_eq (q := 4) (m := m) (n := n) (x := x) (a := a) (y := y)
                          (hxy := h_proper a ha)
                        simpa [xy, add_assoc] using this

                      /-
                      -- Sum the expansion over `allowSet` and swap the order of summation.
                      have h_allow_split :
                          (∑ a ∈ allowSet, B (insert1 x a y))
                            = (∑ i : Fin (m + 1), ∑ a ∈ allowSet, B (insert1 (erase (n := m) x i) a y))\n+                                + (allowSet.card * B xy)\n+                                + ∑ j : Fin (n + 1), ∑ a ∈ allowSet, B (insert1 x a (erase (n := n) y j)) := by\n+                        calc\n+                          (∑ a ∈ allowSet, B (insert1 x a y))\n+                              = ∑ a ∈ allowSet,\n+                                  ((∑ i : Fin (m + 1), B (insert1 (erase (n := m) x i) a y))\n+                                    + B xy\n+                                    + ∑ j : Fin (n + 1), B (insert1 x a (erase (n := n) y j))) := by\n+                                  refine Finset.sum_congr rfl ?_\n+                                  intro a ha\n+                                  simpa [h_expand a ha]\n+                          _ = (∑ i : Fin (m + 1), ∑ a ∈ allowSet, B (insert1 (erase (n := m) x i) a y))\n+                                + (∑ a ∈ allowSet, B xy)\n+                                + ∑ j : Fin (n + 1), ∑ a ∈ allowSet, B (insert1 x a (erase (n := n) y j)) := by\n+                                  -- Distribute and swap the double sums.\n+                                  have hdistrib :\n+                                      (∑ a ∈ allowSet,\n+                                          ((∑ i : Fin (m + 1), B (insert1 (erase (n := m) x i) a y))\n+                                            + B xy\n+                                            + ∑ j : Fin (n + 1), B (insert1 x a (erase (n := n) y j))))\n+                                        = (∑ a ∈ allowSet, ∑ i : Fin (m + 1), B (insert1 (erase (n := m) x i) a y))\n+                                            + (∑ a ∈ allowSet, B xy)\n+                                            + (∑ a ∈ allowSet, ∑ j : Fin (n + 1), B (insert1 x a (erase (n := n) y j))) := by\n+                                    calc\n+                                      (∑ a ∈ allowSet,\n+                                            ((∑ i : Fin (m + 1), B (insert1 (erase (n := m) x i) a y))\n+                                              + B xy\n+                                              + ∑ j : Fin (n + 1), B (insert1 x a (erase (n := n) y j))))\n+                                          = ∑ a ∈ allowSet,\n+                                              ((∑ i : Fin (m + 1), B (insert1 (erase (n := m) x i) a y))\n+                                                + (B xy + ∑ j : Fin (n + 1), B (insert1 x a (erase (n := n) y j)))) := by\n+                                                refine Finset.sum_congr rfl ?_\n+                                                intro a ha\n+                                                ac_rfl\n+                                      _ = (∑ a ∈ allowSet, (∑ i : Fin (m + 1), B (insert1 (erase (n := m) x i) a y)))\n+                                            + ∑ a ∈ allowSet, (B xy + ∑ j : Fin (n + 1), B (insert1 x a (erase (n := n) y j))) := by\n+                                                simp [Finset.sum_add_distrib]\n+                                      _ = (∑ a ∈ allowSet, (∑ i : Fin (m + 1), B (insert1 (erase (n := m) x i) a y)))\n+                                            + ((∑ a ∈ allowSet, B xy)\n+                                                + (∑ a ∈ allowSet, ∑ j : Fin (n + 1), B (insert1 x a (erase (n := n) y j)))) := by\n+                                                simp [Finset.sum_add_distrib]\n+                                      _ = _ := by\n+                                                ac_rfl\n+\n+                                  have hswap_left :\n+                                      (∑ a ∈ allowSet, ∑ i : Fin (m + 1), B (insert1 (erase (n := m) x i) a y))\n+                                        = ∑ i : Fin (m + 1), ∑ a ∈ allowSet, B (insert1 (erase (n := m) x i) a y) := by\n+                                    simpa using\n+                                      (Finset.sum_comm (s := allowSet) (t := (Finset.univ : Finset (Fin (m + 1))))\n+                                        (f := fun a i => B (insert1 (erase (n := m) x i) a y)))\n+\n+                                  have hswap_right :\n+                                      (∑ a ∈ allowSet, ∑ j : Fin (n + 1), B (insert1 x a (erase (n := n) y j)))\n+                                        = ∑ j : Fin (n + 1), ∑ a ∈ allowSet, B (insert1 x a (erase (n := n) y j)) := by\n+                                    simpa using\n+                                      (Finset.sum_comm (s := allowSet) (t := (Finset.univ : Finset (Fin (n + 1))))\n+                                        (f := fun a j => B (insert1 x a (erase (n := n) y j))))\n+\n+                                  calc\n+                                    (∑ a ∈ allowSet,\n+                                          ((∑ i : Fin (m + 1), B (insert1 (erase (n := m) x i) a y))\n+                                            + B xy\n+                                            + ∑ j : Fin (n + 1), B (insert1 x a (erase (n := n) y j))))\n+                                        = (∑ a ∈ allowSet, ∑ i : Fin (m + 1), B (insert1 (erase (n := m) x i) a y))\n+                                            + (∑ a ∈ allowSet, B xy)\n+                                            + (∑ a ∈ allowSet, ∑ j : Fin (n + 1), B (insert1 x a (erase (n := n) y j))) := by\n+                                            simpa using hdistrib\n+                                    _ = (∑ i : Fin (m + 1), ∑ a ∈ allowSet, B (insert1 (erase (n := m) x i) a y))\n+                                          + (∑ a ∈ allowSet, B xy)\n+                                          + (∑ j : Fin (n + 1), ∑ a ∈ allowSet, B (insert1 x a (erase (n := n) y j))) := by\n+                                            rw [hswap_left, hswap_right]\n+                          _ = (∑ i : Fin (m + 1), ∑ a ∈ allowSet, B (insert1 (erase (n := m) x i) a y))\n+                                + (allowSet.card * B xy)\n+                                + ∑ j : Fin (n + 1), ∑ a ∈ allowSet, B (insert1 x a (erase (n := n) y j)) := by\n+                                  simp [Finset.sum_const_nat]\n+\n+                      -- Evaluate the `i`-sum. Split off the last deletion index.\n+                      have hx_sum_cast (i : Fin m) :\n+                          (∑ a ∈ allowSet, B (insert1 (erase (n := m) x i.castSucc) a y))\n+                            = 2 * choose (m + n + 3) (m + 1) * B (erase (n := m) x i.castSucc) * B y := by\n+                        -- The excluded colors `xm` and `y1` contribute 0.\n+                        have hx_last : (erase (n := m) x i.castSucc) (Fin.last (m - 1)) = xm := by\n+                          cases m with\n+                          | zero => cases i.elim0\n+                          | succ m =>\n+                              -- `i : Fin (m + 1)` and `x : Word 4 (m + 2)`.\n+                              simpa [xm] using\n+                                (Word.erase_castSucc_last (q := 4) (n := m) (x := x) (i := i))\n+\n+                        have h_missing_xm : B (insert1 (erase (n := m) x i.castSucc) xm y) = 0 := by\n+                          -- Rewrite `xm` as the last letter of the erased word.\n+                          have hx_last' : xm = (erase (n := m) x i.castSucc) (Fin.last (m - 1)) := by\n+                            simpa using hx_last.symm\n+                          -- Now apply `B_insert1_eq_zero_of_eq_last`.\n+                          cases m with\n+                          | zero => cases i.elim0\n+                          | succ m =>\n+                              simpa [hx_last'] using\n+                                (B_insert1_eq_zero_of_eq_last (m := m) (n := n)\n+                                  (x := erase (n := Nat.succ m) x i.castSucc) (y := y))\n+\n+                        have h_missing_y1 : B (insert1 (erase (n := m) x i.castSucc) y1 y) = 0 := by\n+                          simpa [y1] using\n+                            (B_insert1_eq_zero_of_eq_first (x := erase (n := m) x i.castSucc) (y := y))\n+\n+                        have hab : y1 ≠ xm := (ne_comm).1 hxy\n+                        have hfull :\n+                            (∑ a : Fin 4, B (insert1 (erase (n := m) x i.castSucc) a y))\n+                              = ∑ a ∈ allowSet, B (insert1 (erase (n := m) x i.castSucc) a y) := by\n+                          simpa [allowSet] using\n+                            (sum_univ_eq_sum_erase_erase (a := xm) (b := y1) (hab := hab)\n+                              (f := fun a => B (insert1 (erase (n := m) x i.castSucc) a y))\n+                              (hfa := h_missing_xm) (hfb := h_missing_y1))\n+\n+                        have hih :=\n+                          ih (m := m) (n := n + 1) (x := erase (n := m) x i.castSucc) (y := y) hkx\n+                        calc\n+                          (∑ a ∈ allowSet, B (insert1 (erase (n := m) x i.castSucc) a y))\n+                              = ∑ a : Fin 4, B (insert1 (erase (n := m) x i.castSucc) a y) := by\n+                                  simpa using hfull.symm\n+                          _ = 2 * choose (m + (n + 1) + 2) (m + 1) * B (erase (n := m) x i.castSucc) * B y := by\n+                                  simpa using hih\n+                          _ = 2 * choose (m + n + 3) (m + 1) * B (erase (n := m) x i.castSucc) * B y := by\n+                                  simp [Nat.add_assoc]\n+\n+                      have hx_sum_last :\n+                          (∑ a ∈ allowSet, B (insert1 (erase (n := m) x (Fin.last m)) a y))\n+                              + B xy\n+                            = 2 * choose (m + n + 3) (m + 1) * B (erase (n := m) x (Fin.last m)) * B y := by\n+                        -- Let `f a = B (insert1 (erase x last) a y)`.\n+                        let f : Fin 4 → ℕ := fun a => B (insert1 (erase (n := m) x (Fin.last m)) a y)\n+                        have hab : y1 ≠ xm := (ne_comm).1 hxy\n+                        have hf_y1 : f y1 = 0 := by\n+                          -- Boundary failure for `a = y1`.\n+                          simpa [f, y1] using\n+                            (B_insert1_eq_zero_of_eq_first (x := erase (n := m) x (Fin.last m)) (y := y))\n+                        have hf_xm : f xm = B xy := by\n+                          -- Inserting `xm` after deleting the last position gives back `xy`.\n+                          simpa [f, xm, xy] using\n+                            (B_insert1_erase_last_eq_B_append (m := m) (n := n) (x := x) (y := y))\n+\n+                        have hy_mem : y1 ∈ (Finset.univ.erase xm) := by\n+                          simp [Finset.mem_erase, hab]\n+                        -- Decompose the full sum by erasing `xm` then `y1`.\n+                        have hsum_xm :=\n+                          (Finset.sum_erase_add (s := (Finset.univ : Finset (Fin 4)))\n+                            (a := xm) (f := f) (Finset.mem_univ xm))\n+                        have hsum_y1 :=\n+                          (Finset.sum_erase_add (s := (Finset.univ.erase xm))\n+                            (a := y1) (f := f) hy_mem)\n+\n+                        have hfull :\n+                            (∑ a : Fin 4, f a) = (∑ a ∈ allowSet, f a) + f xm := by\n+                          -- `∑ univ f = ∑ (univ.erase xm) f + f xm` and `∑ (univ.erase xm) f = ∑ allowSet f + f y1`.\n+                          calc\n+                            (∑ a : Fin 4, f a)\n+                                = (∑ a ∈ (Finset.univ.erase xm), f a) + f xm := by\n+                                    simpa using hsum_xm.symm\n+                            _ = ((∑ a ∈ allowSet, f a) + f y1) + f xm := by\n+                                    -- Rewrite the sum over `univ.erase xm` using `hsum_y1`.\n+                                    simpa [allowSet] using congrArg (fun t => t + f xm) hsum_y1.symm\n+                            _ = (∑ a ∈ allowSet, f a) + f xm := by\n+                                    simp [hf_y1, add_assoc]\n+\n+                        -- Use the induction hypothesis on the full sum.\n+                        have hih :=\n+                          ih (m := m) (n := n + 1) (x := erase (n := m) x (Fin.last m)) (y := y) hkx\n+                        have hfull' :\n+                            (∑ a ∈ allowSet, f a) + B xy = ∑ a : Fin 4, f a := by\n+                          -- Rewrite `B xy` as `f xm`.\n+                          calc\n+                            (∑ a ∈ allowSet, f a) + B xy\n+                                = (∑ a ∈ allowSet, f a) + f xm := by\n+                                    simpa [hf_xm]\n+                            _ = ∑ a : Fin 4, f a := by\n+                                    exact hfull.symm\n+\n+                        -- Finish by rewriting and simplifying.\n+                        calc\n+                          (∑ a ∈ allowSet, B (insert1 (erase (n := m) x (Fin.last m)) a y)) + B xy\n+                              = (∑ a ∈ allowSet, f a) + B xy := by\n+                                  rfl\n+                          _ = ∑ a : Fin 4, f a := hfull'\n+                          _ = 2 * choose (m + (n + 1) + 2) (m + 1) * B (erase (n := m) x (Fin.last m)) * B y := by\n+                                  simpa [f] using hih\n+                          _ = 2 * choose (m + n + 3) (m + 1) * B (erase (n := m) x (Fin.last m)) * B y := by\n+                                  simp [Nat.add_assoc]\n+\n+                      -- Evaluate the `j`-sum. Split off `j = 0`.\n+                      have hy_sum_succ (j : Fin n) :\n+                          (∑ a ∈ allowSet, B (insert1 x a (erase (n := n) y j.succ)))\n+                            = 2 * choose (m + n + 3) (m + 2) * B x * B (erase (n := n) y j.succ) := by\n+                        -- Show the excluded colors contribute 0.\n+                        have h_missing_xm : B (insert1 x xm (erase (n := n) y j.succ)) = 0 := by\n+                          simpa [xm] using\n+                            (B_insert1_eq_zero_of_eq_last (m := m) (n := n - 1)\n+                              (x := x) (y := erase (n := n) y j.succ))\n+\n+                        have hy_first : (erase (n := n) y j.succ) 0 = y1 := by\n+                          cases n with\n+                          | zero => cases j.elim0\n+                          | succ n =>\n+                              -- Apply `erase_succ_zero`.\n+                              simpa [y1] using\n+                                (Word.erase_succ_zero (q := 4) (n := n) (x := y) (i := j))\n+\n+                        have h_missing_y1 : B (insert1 x y1 (erase (n := n) y j.succ)) = 0 := by\n+                          -- Rewrite `y1` as the first letter of the erased word.\n+                          have : y1 = (erase (n := n) y j.succ) 0 := by\n+                            simpa using hy_first.symm\n+                          simpa [this] using\n+                            (B_insert1_eq_zero_of_eq_first (x := x) (y := erase (n := n) y j.succ))\n+\n+                        have hab : y1 ≠ xm := (ne_comm).1 hxy\n+                        have hfull :\n+                            (∑ a : Fin 4, B (insert1 x a (erase (n := n) y j.succ)))\n+                              = ∑ a ∈ allowSet, B (insert1 x a (erase (n := n) y j.succ)) := by\n+                          simpa [allowSet] using\n+                            (sum_univ_eq_sum_erase_erase (a := xm) (b := y1) (hab := hab)\n+                              (f := fun a => B (insert1 x a (erase (n := n) y j.succ)))\n+                              (hfa := h_missing_xm) (hfb := h_missing_y1))\n+\n+                        have hih :=\n+                          ih (m := m + 1) (n := n) (x := x) (y := erase (n := n) y j.succ) hky\n+                        calc\n+                          (∑ a ∈ allowSet, B (insert1 x a (erase (n := n) y j.succ)))\n+                              = ∑ a : Fin 4, B (insert1 x a (erase (n := n) y j.succ)) := by\n+                                  simpa using hfull.symm\n+                          _ = 2 * choose ((m + 1) + n + 2) ((m + 1) + 1) * B x * B (erase (n := n) y j.succ) := by\n+                                  simpa using hih\n+                          _ = 2 * choose (m + n + 3) (m + 2) * B x * B (erase (n := n) y j.succ) := by\n+                                  have h₁ : (m + 1) + n + 2 = m + n + 3 := by\n+                                    ac_rfl\n+                                  have h₂ : (m + 1) + 1 = m + 2 := by\n+                                    simp [Nat.add_assoc]\n+                                  simp [h₁, h₂]\n+\n+                      have hy_sum_zero :\n+                          (∑ a ∈ allowSet, B (insert1 x a (erase (n := n) y 0))) + B xy\n+                            = 2 * choose (m + n + 3) (m + 2) * B x * B (erase (n := n) y 0) := by\n+                        -- Let `f a = B (insert1 x a (erase y 0))`.\n+                        let f : Fin 4 → ℕ := fun a => B (insert1 x a (erase (n := n) y 0))\n+                        have hab : y1 ≠ xm := (ne_comm).1 hxy\n+                        have hf_xm : f xm = 0 := by\n+                          simpa [f, xm] using\n+                            (B_insert1_eq_zero_of_eq_last (m := m) (n := n - 1)\n+                              (x := x) (y := erase (n := n) y 0))\n+                        have hf_y1 : f y1 = B xy := by\n+                          -- Inserting `y1` before `erase y 0` gives `xy`.\n+                          simpa [f, y1, xy] using\n+                            (B_append_eq_B_insert1_erase_zero (m := m) (n := n) (x := x) (y := y))\n+\n+                        have hy_mem : y1 ∈ (Finset.univ.erase xm) := by\n+                          simp [Finset.mem_erase, hab]\n+                        have hsum_xm :=\n+                          (Finset.sum_erase_add (s := (Finset.univ : Finset (Fin 4)))\n+                            (a := xm) (f := f) (Finset.mem_univ xm))\n+                        have hsum_y1 :=\n+                          (Finset.sum_erase_add (s := (Finset.univ.erase xm))\n+                            (a := y1) (f := f) hy_mem)\n+\n+                        have hfull :\n+                            (∑ a : Fin 4, f a) = (∑ a ∈ allowSet, f a) + f y1 := by\n+                          calc\n+                            (∑ a : Fin 4, f a)\n+                                = (∑ a ∈ (Finset.univ.erase xm), f a) + f xm := by\n+                                    simpa using hsum_xm.symm\n+                            _ = ((∑ a ∈ allowSet, f a) + f y1) + f xm := by\n+                                    simpa [allowSet] using congrArg (fun t => t + f xm) hsum_y1.symm\n+                            _ = (∑ a ∈ allowSet, f a) + f y1 := by\n+                                    simp [hf_xm, add_assoc]\n+\n+                        have hih :=\n+                          ih (m := m + 1) (n := n) (x := x) (y := erase (n := n) y 0) hky\n+\n+                        have hfull' : (∑ a ∈ allowSet, f a) + B xy = ∑ a : Fin 4, f a := by\n+                          calc\n+                            (∑ a ∈ allowSet, f a) + B xy\n+                                = (∑ a ∈ allowSet, f a) + f y1 := by\n+                                    simpa [hf_y1]\n+                            _ = ∑ a : Fin 4, f a := by\n+                                    exact hfull.symm\n+\n+                        calc\n+                          (∑ a ∈ allowSet, B (insert1 x a (erase (n := n) y 0))) + B xy\n+                              = (∑ a ∈ allowSet, f a) + B xy := by\n+                                  rfl\n+                          _ = ∑ a : Fin 4, f a := hfull'\n+                          _ = 2 * choose ((m + 1) + n + 2) ((m + 1) + 1) * B x * B (erase (n := n) y 0) := by\n+                                  simpa [f] using hih\n+                          _ = 2 * choose (m + n + 3) (m + 2) * B x * B (erase (n := n) y 0) := by\n+                                  have h₁ : (m + 1) + n + 2 = m + n + 3 := by\n+                                    ac_rfl\n+                                  have h₂ : (m + 1) + 1 = m + 2 := by\n+                                    simp [Nat.add_assoc]\n+                                  simp [h₁, h₂]\n+\n+                      -- Put the pieces together for the `i`-sum.\n+                      have hx_total :\n+                          (∑ i : Fin (m + 1), ∑ a ∈ allowSet, B (insert1 (erase (n := m) x i) a y))\n+                              + B xy\n+                            = 2 * choose (m + n + 3) (m + 1) * B x * B y := by\n+                        -- Split the `i` sum into castSucc and the last index, then use `hxB`.\n+                        have hx_cast :\n+                            (∑ i : Fin (m + 1), ∑ a ∈ allowSet, B (insert1 (erase (n := m) x i) a y))\n+                              = (∑ i : Fin m, ∑ a ∈ allowSet, B (insert1 (erase (n := m) x i.castSucc) a y))\n+                                  + ∑ a ∈ allowSet, B (insert1 (erase (n := m) x (Fin.last m)) a y) := by\n+                          simpa [Fin.sum_univ_castSucc]\n+                        -- Evaluate the cast-succ part.\n+                        have hx_cast_eval :\n+                            (∑ i : Fin m, ∑ a ∈ allowSet, B (insert1 (erase (n := m) x i.castSucc) a y))\n+                              = ∑ i : Fin m, 2 * choose (m + n + 3) (m + 1) * B (erase (n := m) x i.castSucc) * B y := by\n+                          refine Fintype.sum_congr _ _ ?_\n+                          intro i\n+                          simpa using hx_sum_cast i\n+                        -- Evaluate the last term using `hx_sum_last`.\n+                        calc\n+                          (∑ i : Fin (m + 1), ∑ a ∈ allowSet, B (insert1 (erase (n := m) x i) a y)) + B xy\n+                              = ((∑ i : Fin m, ∑ a ∈ allowSet, B (insert1 (erase (n := m) x i.castSucc) a y))\n+                                  + (∑ a ∈ allowSet, B (insert1 (erase (n := m) x (Fin.last m)) a y))) + B xy := by\n+                                  simpa [hx_cast, add_assoc]\n+                          _ = (∑ i : Fin m, 2 * choose (m + n + 3) (m + 1) * B (erase (n := m) x i.castSucc) * B y)\n+                                  + (2 * choose (m + n + 3) (m + 1) * B (erase (n := m) x (Fin.last m)) * B y) := by\n+                                  -- Replace each part.\n+                                  rw [hx_cast_eval]\n+                                  -- `hx_sum_last` rewrites the last term plus `B xy`.\n+                                  simpa [add_assoc] using congrArg (fun t => (∑ i : Fin m, 2 * choose (m + n + 3) (m + 1)\n+                                    * B (erase (n := m) x i.castSucc) * B y) + t) hx_sum_last\n+                          _ = 2 * choose (m + n + 3) (m + 1) * (∑ i : Fin (m + 1), B (erase (n := m) x i)) * B y := by\n+                                  -- Combine into a single sum over `Fin (m+1)`.\n+                                  have :\n+                                      (∑ i : Fin (m + 1), B (erase (n := m) x i))\n+                                        = (∑ i : Fin m, B (erase (n := m) x i.castSucc)) + B (erase (n := m) x (Fin.last m)) := by\n+                                          simpa using (Fin.sum_univ_castSucc (f := fun i : Fin (m + 1) => B (erase (n := m) x i)))\n+                                  -- Now factor out constants.\n+                                  simp [this, Nat.mul_assoc, Nat.mul_left_comm, Nat.mul_comm, Nat.add_assoc, Nat.add_left_comm,\n+                                    Nat.add_comm, Nat.add_mul, Nat.mul_add]\n+                          _ = 2 * choose (m + n + 3) (m + 1) * B x * B y := by\n+                                  -- Replace the erasure sum by `B x`.\n+                                  simpa [hxB, Nat.mul_assoc, Nat.mul_left_comm, Nat.mul_comm]\n+\n+                      -- Put the pieces together for the `j`-sum.\n+                      have hy_total :\n+                          (∑ j : Fin (n + 1), ∑ a ∈ allowSet, B (insert1 x a (erase (n := n) y j)))\n+                              + B xy\n+                            = 2 * choose (m + n + 3) (m + 2) * B x * B y := by\n+                        -- Split the `j` sum into `0` and successors.\n+                        have hy_split :\n+                            (∑ j : Fin (n + 1), ∑ a ∈ allowSet, B (insert1 x a (erase (n := n) y j)))\n+                              = (∑ a ∈ allowSet, B (insert1 x a (erase (n := n) y 0)))\n+                                  + ∑ j : Fin n, ∑ a ∈ allowSet, B (insert1 x a (erase (n := n) y j.succ)) := by\n+                          simpa [Fin.sum_univ_succ]\n+                        have hy_succ_eval :\n+                            (∑ j : Fin n, ∑ a ∈ allowSet, B (insert1 x a (erase (n := n) y j.succ)))\n+                              = ∑ j : Fin n, 2 * choose (m + n + 3) (m + 2) * B x * B (erase (n := n) y j.succ) := by\n+                          refine Fintype.sum_congr _ _ ?_\n+                          intro j\n+                          simpa using hy_sum_succ j\n+                        calc\n+                          (∑ j : Fin (n + 1), ∑ a ∈ allowSet, B (insert1 x a (erase (n := n) y j))) + B xy\n+                              = ((∑ a ∈ allowSet, B (insert1 x a (erase (n := n) y 0)))\n+                                  + (∑ j : Fin n, ∑ a ∈ allowSet, B (insert1 x a (erase (n := n) y j.succ)))) + B xy := by\n+                                  simpa [hy_split, add_assoc]\n+                          _ = (2 * choose (m + n + 3) (m + 2) * B x * B (erase (n := n) y 0))\n+                                  + (∑ j : Fin n, 2 * choose (m + n + 3) (m + 2) * B x * B (erase (n := n) y j.succ)) := by\n+                                  -- Use `hy_sum_zero` and `hy_succ_eval`.\n+                                  rw [hy_succ_eval]\n+                                  -- `hy_sum_zero` rewrites the first term plus `B xy`.\n+                                  simpa [add_assoc] using congrArg (fun t => t + (∑ j : Fin n, 2 * choose (m + n + 3) (m + 2)\n+                                    * B x * B (erase (n := n) y j.succ))) hy_sum_zero\n+                          _ = 2 * choose (m + n + 3) (m + 2) * B x * (∑ j : Fin (n + 1), B (erase (n := n) y j)) := by\n+                                  -- Combine the sums over `j`.\n+                                  have :\n+                                      (∑ j : Fin (n + 1), B (erase (n := n) y j))\n+                                        = B (erase (n := n) y 0)\n+                                            + (∑ j : Fin n, B (erase (n := n) y j.succ)) := by\n+                                          simpa using (Fin.sum_univ_succ (f := fun j : Fin (n + 1) => B (erase (n := n) y j)))\n+                                  -- Factor out constants.\n+                                  simp [this, Nat.mul_assoc, Nat.mul_left_comm, Nat.mul_comm, Nat.add_assoc, Nat.add_left_comm,\n+                                    Nat.add_comm, Nat.mul_add, Nat.add_mul]\n+                          _ = 2 * choose (m + n + 3) (m + 2) * B x * B y := by\n+                                  -- Replace the erasure sum by `B y`.\n+                                  simpa [hyB, Nat.mul_assoc, Nat.mul_left_comm, Nat.mul_comm]\n+\n+                      -- Assemble the full sum using the split expression and the two completed sums.\n+                      have h_allow :\n+                          (∑ a ∈ allowSet, B (insert1 x a y))\n+                            = 2 * (choose (m + n + 3) (m + 1) + choose (m + n + 3) (m + 2)) * B x * B y := by\n+                        -- Start from `h_allow_split`.\n+                        have :\n+                            (∑ a ∈ allowSet, B (insert1 x a y))\n+                              = (∑ i : Fin (m + 1), ∑ a ∈ allowSet, B (insert1 (erase (n := m) x i) a y))\n+                                  + (allowSet.card * B xy)\n+                                  + (∑ j : Fin (n + 1), ∑ a ∈ allowSet, B (insert1 x a (erase (n := n) y j))) := by\n+                            exact h_allow_split\n+\n+                        -- Rewrite `allowSet.card * B xy` as `B xy + B xy` and use `hx_total`/`hy_total`.\n+                        calc\n+                          (∑ a ∈ allowSet, B (insert1 x a y))\n+                              = (∑ i : Fin (m + 1), ∑ a ∈ allowSet, B (insert1 (erase (n := m) x i) a y))\n+                                  + (allowSet.card * B xy)\n+                                  + (∑ j : Fin (n + 1), ∑ a ∈ allowSet, B (insert1 x a (erase (n := n) y j))) := this\n+                          _ = (∑ i : Fin (m + 1), ∑ a ∈ allowSet, B (insert1 (erase (n := m) x i) a y))\n+                                  + (B xy + B xy)\n+                                  + (∑ j : Fin (n + 1), ∑ a ∈ allowSet, B (insert1 x a (erase (n := n) y j))) := by\n+                                    -- Use `hcard`.\n+                                    simp [hcard, two_mul, add_assoc, add_left_comm, add_comm]\n+                          _ = (2 * choose (m + n + 3) (m + 1) * B x * B y)\n+                                  + (2 * choose (m + n + 3) (m + 2) * B x * B y) := by\n+                                    -- Use `hx_total` and `hy_total`, each consuming one `B xy`.\n+                                    -- Rearrange terms carefully.\n+                                    have h1 :\n+                                        (∑ i : Fin (m + 1), ∑ a ∈ allowSet, B (insert1 (erase (n := m) x i) a y)) + B xy\n+                                          = 2 * choose (m + n + 3) (m + 1) * B x * B y := by\n+                                        simpa using hx_total\n+                                    have h2 :\n+                                        (∑ j : Fin (n + 1), ∑ a ∈ allowSet, B (insert1 x a (erase (n := n) y j))) + B xy\n+                                          = 2 * choose (m + n + 3) (m + 2) * B x * B y := by\n+                                        simpa using hy_total\n+                                    -- Combine `h1` and `h2`.\n+                                    -- Start from the LHS and group as `(i-sum + Bxy) + (j-sum + Bxy)`.\n+                                    calc\n+                                      (∑ i : Fin (m + 1), ∑ a ∈ allowSet, B (insert1 (erase (n := m) x i) a y))\n+                                          + (B xy + B xy)\n+                                          + (∑ j : Fin (n + 1), ∑ a ∈ allowSet, B (insert1 x a (erase (n := n) y j)))\n+                                          = ((∑ i : Fin (m + 1), ∑ a ∈ allowSet, B (insert1 (erase (n := m) x i) a y)) + B xy)\n+                                              + ((∑ j : Fin (n + 1), ∑ a ∈ allowSet, B (insert1 x a (erase (n := n) y j))) + B xy) := by\n+                                                ac_rfl\n+                                      _ = (2 * choose (m + n + 3) (m + 1) * B x * B y)\n+                                            + (2 * choose (m + n + 3) (m + 2) * B x * B y) := by\n+                                                simp [h1, h2]\n+                          _ = 2 * (choose (m + n + 3) (m + 1) + choose (m + n + 3) (m + 2)) * B x * B y := by\n+                                    -- Factor out `2 * ... * B x * B y`.\n+                                    simp [Nat.mul_add, Nat.add_mul, Nat.mul_assoc, Nat.mul_left_comm, Nat.mul_comm,\n+                                      add_assoc, add_left_comm, add_comm]\n+\n+                      have hpascal :\n+                          choose (m + n + 4) (m + 2)\n+                            = choose (m + n + 3) (m + 1) + choose (m + n + 3) (m + 2) := by\n+                        simpa [Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using\n+                          (Nat.choose_succ_succ' (n := m + n + 3) (k := m + 1))\n+\n+                      have hchoose :\n+                          2 * choose (m + n + 4) (m + 2) * B x * B y\n+                            = 2 * choose ((m + 1) + (n + 1) + 2) ((m + 1) + 1) * B x * B y := by\n+                        have h₁ : m + n + 4 = (m + 1) + (n + 1) + 2 := by\n+                          ac_rfl\n+                        have h₂ : m + 2 = (m + 1) + 1 := by\n+                          simp [Nat.add_assoc]\n+                        simp [h₁, h₂]\n+\n+                      -- Finish.\n+                      calc\n+                        (∑ a : Fin 4, B (insert1 x a y))\n+                            = ∑ a ∈ allowSet, B (insert1 x a y) := h_sum\n+                        _ = 2 * (choose (m + n + 3) (m + 1) + choose (m + n + 3) (m + 2)) * B x * B y := h_allow\n+                        _ = 2 * choose (m + n + 4) (m + 2) * B x * B y := by\n+                              simp [hpascal, Nat.mul_assoc, Nat.mul_left_comm, Nat.mul_comm]\n+                        _ = 2 * choose ((m + 1) + (n + 1) + 2) ((m + 1) + 1) * B x * B y := by\n+                              simpa [hchoose]\n                   · -- `y` not proper: both sides are zero.\n                     have hyB0 : B y = 0 := B_eq_zero_of_not_isProper (q := 4) (x := y) (n := n) hy\n                     have hterm (a : Fin 4) : B (insert1 x a y) = 0 := by\n                       have hnot : ¬ IsProper (insert1 x a y) := by\n*** End Patch
                      -/

                      -- Sum the expansion over `allowSet` and swap the order of summation.
                      have h_allow_split :
                          (∑ a ∈ allowSet, B (insert1 x a y))
                            = (∑ i : Fin (m + 1), ∑ a ∈ allowSet,
                                  B (insert1 (erase (n := m) x i) a y))
                                + (allowSet.card * B xy)
                                + (∑ j : Fin (n + 1), ∑ a ∈ allowSet,
                                  B (insert1 x a (erase (n := n) y j))) := by
                        calc
                          (∑ a ∈ allowSet, B (insert1 x a y))
                              = ∑ a ∈ allowSet,
                                  ((∑ i : Fin (m + 1), B (insert1 (erase (n := m) x i) a y))
                                    + B xy
                                    + ∑ j : Fin (n + 1), B (insert1 x a (erase (n := n) y j))) := by
                                  refine Finset.sum_congr rfl ?_
                                  intro a ha
                                  simp [h_expand a ha]
                          _ = (∑ a ∈ allowSet, ∑ i : Fin (m + 1),
                                  B (insert1 (erase (n := m) x i) a y))
                                + (∑ a ∈ allowSet, B xy)
                                + (∑ a ∈ allowSet, ∑ j : Fin (n + 1),
                                  B (insert1 x a (erase (n := n) y j))) := by
                                  simp [Finset.sum_add_distrib, add_assoc, add_comm]
                          _ = (∑ i : Fin (m + 1), ∑ a ∈ allowSet,
                                  B (insert1 (erase (n := m) x i) a y))
                                + (∑ a ∈ allowSet, B xy)
                                + (∑ j : Fin (n + 1), ∑ a ∈ allowSet,
                                  B (insert1 x a (erase (n := n) y j))) := by
                                  have hswap_left :
                                      (∑ a ∈ allowSet, ∑ i : Fin (m + 1),
                                          B (insert1 (erase (n := m) x i) a y))
                                        = (∑ i : Fin (m + 1), ∑ a ∈ allowSet,
                                          B (insert1 (erase (n := m) x i) a y)) := by
                                    simpa using
                                      (Finset.sum_comm (s := allowSet)
                                        (t := (Finset.univ : Finset (Fin (m + 1))))
                                        (f := fun a i => B (insert1 (erase (n := m) x i) a y)))
                                  have hswap_right :
                                      (∑ a ∈ allowSet, ∑ j : Fin (n + 1),
                                          B (insert1 x a (erase (n := n) y j)))
                                        = (∑ j : Fin (n + 1), ∑ a ∈ allowSet,
                                          B (insert1 x a (erase (n := n) y j))) := by
                                    simpa using
                                      (Finset.sum_comm (s := allowSet)
                                        (t := (Finset.univ : Finset (Fin (n + 1))))
                                        (f := fun a j => B (insert1 x a (erase (n := n) y j))))
                                  rw [hswap_left, hswap_right]
                          _ = (∑ i : Fin (m + 1), ∑ a ∈ allowSet,
                                  B (insert1 (erase (n := m) x i) a y))
                                + (allowSet.card * B xy)
                                + (∑ j : Fin (n + 1), ∑ a ∈ allowSet,
                                  B (insert1 x a (erase (n := n) y j))) := by
                                  simp

                      have hx_total :
                          (∑ i : Fin (m + 1), ∑ a ∈ allowSet,
                                B (insert1 (erase (n := m) x i) a y)) + B xy
                            = 2 * choose (m + n + 3) (m + 1) * B x * B y := by
                        have hab : y1 ≠ xm := (ne_comm).1 hxy
                        have h_reassemble :
                            (∑ i : Fin (m + 1), ∑ a ∈ allowSet,
                                B (insert1 (erase (n := m) x i) a y)) + B xy
                              = ∑ i : Fin (m + 1), ∑ a : Fin 4,
                                  B (insert1 (erase (n := m) x i) a y) := by
                          let g : Fin (m + 1) → Nat :=
                            fun i => ∑ a ∈ allowSet, B (insert1 (erase (n := m) x i) a y)
                          let h : Fin (m + 1) → Nat :=
                            fun i => ∑ a : Fin 4, B (insert1 (erase (n := m) x i) a y)

                          have hcast (i : Fin m) : g i.castSucc = h i.castSucc := by
                            have h_missing_y1 :
                                B (insert1 (erase (n := m) x i.castSucc) y1 y) = 0 := by
                              simpa [y1] using
                                B_insert1_eq_zero_of_eq_first (x := erase (n := m) x i.castSucc) (y := y)
                            have h_missing_xm :
                                B (insert1 (erase (n := m) x i.castSucc) xm y) = 0 := by
                              cases m with
                              | zero =>
                                  exact i.elim0
                              | succ m =>
                                  have hlast :
                                      (erase (n := Nat.succ m) x i.castSucc) (Fin.last m) = xm := by
                                    simp [xm]
                                  simpa [hlast.symm] using
                                    (B_insert1_eq_zero_of_eq_last (m := m) (n := n)
                                      (x := erase (n := Nat.succ m) x i.castSucc) (y := y))
                            have hfull :
                                (∑ a : Fin 4, B (insert1 (erase (n := m) x i.castSucc) a y))
                                  = ∑ a ∈ allowSet,
                                      B (insert1 (erase (n := m) x i.castSucc) a y) := by
                              simpa [allowSet] using
                                (sum_univ_eq_sum_erase_erase (a := xm) (b := y1) (hab := hab)
                                  (f := fun a => B (insert1 (erase (n := m) x i.castSucc) a y))
                                  (hfa := h_missing_xm) (hfb := h_missing_y1))
                            simpa [g, h] using hfull.symm

                          have hlast : g (Fin.last m) + B xy = h (Fin.last m) := by
                            let xlast : Word 4 m := erase (n := m) x (Fin.last m)
                            have hy1_zero : B (insert1 xlast y1 y) = 0 := by
                              simpa [xlast, y1] using
                                B_insert1_eq_zero_of_eq_first (x := xlast) (y := y)
                            have hxm_val : B (insert1 xlast xm y) = B xy := by
                              simpa [xlast, xm, xy] using
                                B_insert1_erase_last_eq_B_append (m := m) (n := n) (x := x) (y := y)
                            have hy1_mem : y1 ∈ (Finset.univ.erase xm) := by
                              simp [Finset.mem_erase, hab]
                            have hsum_xm :=
                              (Finset.sum_erase_add (s := (Finset.univ : Finset (Fin 4))) (a := xm)
                                (f := fun a => B (insert1 xlast a y))
                                (Finset.mem_univ xm)).symm
                            have hsum_y1 :=
                              (Finset.sum_erase_add (s := (Finset.univ.erase xm)) (a := y1)
                                (f := fun a => B (insert1 xlast a y)) hy1_mem).symm
                            have huniv :
                                (∑ a : Fin 4, B (insert1 xlast a y))
                                  = (∑ a ∈ allowSet, B (insert1 xlast a y)) + B xy := by
                              calc
                                (∑ a : Fin 4, B (insert1 xlast a y))
                                    = (∑ a ∈ (Finset.univ.erase xm), B (insert1 xlast a y))
                                        + B (insert1 xlast xm y) := by
                                          simpa using hsum_xm
                                _ = ((∑ a ∈ allowSet, B (insert1 xlast a y))
                                      + B (insert1 xlast y1 y))
                                    + B (insert1 xlast xm y) := by
                                      rw [hsum_y1]
                                _ = (∑ a ∈ allowSet, B (insert1 xlast a y)) + B xy := by
                                      simp [hy1_zero, hxm_val, add_comm]
                            simpa [g, h, xlast] using huniv.symm

                          have hsum_cast :
                              (∑ i : Fin m, g i.castSucc) = ∑ i : Fin m, h i.castSucc := by
                            refine Fintype.sum_congr _ _ ?_
                            intro i
                            simpa using hcast i

                          calc
                            (∑ i : Fin (m + 1), g i) + B xy
                                = ((∑ i : Fin m, g i.castSucc) + g (Fin.last m)) + B xy := by
                                    simp [Fin.sum_univ_castSucc, g]
                            _ = (∑ i : Fin m, g i.castSucc) + (g (Fin.last m) + B xy) := by
                                    ac_rfl
                            _ = (∑ i : Fin m, h i.castSucc) + h (Fin.last m) := by
                                    simp [hsum_cast, hlast]
                            _ = ∑ i : Fin (m + 1), h i := by
                                    exact (Fin.sum_univ_castSucc (f := h)).symm

                        calc
                          (∑ i : Fin (m + 1), ∑ a ∈ allowSet,
                                B (insert1 (erase (n := m) x i) a y)) + B xy
                              = ∑ i : Fin (m + 1), ∑ a : Fin 4,
                                  B (insert1 (erase (n := m) x i) a y) := h_reassemble
                          _ = ∑ i : Fin (m + 1),
                                  2 * choose (m + n + 3) (m + 1) * B (erase (n := m) x i) * B y := by
                                  refine Fintype.sum_congr _ _ ?_
                                  intro i
                                  have hih := ih (m := m) (n := n + 1) (x := erase (n := m) x i) (y := y) hkx
                                  simpa [Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using hih
                          _ = 2 * choose (m + n + 3) (m + 1) * B x * B y := by
                                  have hmul :
                                      (∑ i : Fin (m + 1),
                                          (2 * choose (m + n + 3) (m + 1) * B y)
                                            * B (erase (n := m) x i))
                                        = (2 * choose (m + n + 3) (m + 1) * B y)
                                            * (∑ i : Fin (m + 1), B (erase (n := m) x i)) := by
                                    simpa using
                                      (Finset.mul_sum (s := (Finset.univ : Finset (Fin (m + 1))))
                                        (f := fun i : Fin (m + 1) => B (erase (n := m) x i))
                                        (a := 2 * choose (m + n + 3) (m + 1) * B y)).symm
                                  calc
                                    (∑ i : Fin (m + 1),
                                          2 * choose (m + n + 3) (m + 1) * B (erase (n := m) x i) * B y)
                                        = ∑ i : Fin (m + 1),
                                            (2 * choose (m + n + 3) (m + 1) * B y)
                                              * B (erase (n := m) x i) := by
                                              refine Fintype.sum_congr _ _ ?_
                                              intro i
                                              ac_rfl
                                    _ = (2 * choose (m + n + 3) (m + 1) * B y)
                                          * (∑ i : Fin (m + 1), B (erase (n := m) x i)) := hmul
                                    _ = (2 * choose (m + n + 3) (m + 1) * B y) * B x := by
                                          simpa using
                                            congrArg (fun t => (2 * choose (m + n + 3) (m + 1) * B y) * t) hxB.symm
                                    _ = 2 * choose (m + n + 3) (m + 1) * B x * B y := by
                                          ac_rfl

                      have hy_total :
                          (∑ j : Fin (n + 1), ∑ a ∈ allowSet,
                                B (insert1 x a (erase (n := n) y j))) + B xy
                            = 2 * choose (m + n + 3) (m + 2) * B x * B y := by
                        have hab : y1 ≠ xm := (ne_comm).1 hxy
                        have h_reassemble :
                            (∑ j : Fin (n + 1), ∑ a ∈ allowSet,
                                  B (insert1 x a (erase (n := n) y j))) + B xy
                              = ∑ j : Fin (n + 1), ∑ a : Fin 4,
                                  B (insert1 x a (erase (n := n) y j)) := by
                          let g : Fin (n + 1) → Nat :=
                            fun j => ∑ a ∈ allowSet, B (insert1 x a (erase (n := n) y j))
                          let h : Fin (n + 1) → Nat :=
                            fun j => ∑ a : Fin 4, B (insert1 x a (erase (n := n) y j))

                          have hsucc (j : Fin n) : g j.succ = h j.succ := by
                            have h_missing_xm :
                                B (insert1 x xm (erase (n := n) y j.succ)) = 0 := by
                              cases n with
                              | zero =>
                                  exact j.elim0
                              | succ n =>
                                  simpa [xm] using
                                    (B_insert1_eq_zero_of_eq_last (m := m) (n := n) (x := x)
                                      (y := erase (n := Nat.succ n) y j.succ))

                            have h_missing_y1 :
                                B (insert1 x y1 (erase (n := n) y j.succ)) = 0 := by
                              cases n with
                              | zero =>
                                  exact j.elim0
                              | succ n =>
                                  have hfirst : (erase (n := Nat.succ n) y j.succ) 0 = y1 := by
                                    simp [y1]
                                  have h0 :
                                      B
                                          (insert1 x ((erase (n := Nat.succ n) y j.succ) 0)
                                            (erase (n := Nat.succ n) y j.succ)) = 0 := by
                                    simpa using
                                      (B_insert1_eq_zero_of_eq_first (x := x)
                                        (y := erase (n := Nat.succ n) y j.succ))
                                  simpa [hfirst] using h0

                            have hfull :
                                (∑ a : Fin 4, B (insert1 x a (erase (n := n) y j.succ)))
                                  = ∑ a ∈ allowSet,
                                      B (insert1 x a (erase (n := n) y j.succ)) := by
                              simpa [allowSet] using
                                (sum_univ_eq_sum_erase_erase (a := xm) (b := y1) (hab := hab)
                                  (f := fun a => B (insert1 x a (erase (n := n) y j.succ)))
                                  (hfa := h_missing_xm) (hfb := h_missing_y1))
                            simpa [g, h] using hfull.symm

                          have hzero : g 0 + B xy = h 0 := by
                            let y0 : Word 4 n := erase (n := n) y 0
                            have hxm_zero : B (insert1 x xm y0) = 0 := by
                              cases n with
                              | zero =>
                                  have hy0 : y0 = emptyWord := Subsingleton.elim _ _
                                  have hnot : ¬ IsProper (snoc x xm) := by
                                    simpa [xm] using (Word.not_isProper_snoc_self (x := x))
                                  have hB0 : B (snoc x xm) = 0 := by
                                    simpa using
                                      (B_eq_zero_of_not_isProper (q := 4) (x := snoc x xm) (n := m + 1) hnot)
                                  simpa [hy0, insert1_empty_right] using hB0
                              | succ n =>
                                  simpa [y0, xm] using
                                    (B_insert1_eq_zero_of_eq_last (m := m) (n := n) (x := x) (y := y0))
                            have hy1_val : B (insert1 x y1 y0) = B xy := by
                              simpa [y0, xy, y1] using
                                (B_append_eq_B_insert1_erase_zero (m := m) (n := n) x y).symm
                            have hy1_mem : y1 ∈ (Finset.univ.erase xm) := by
                              simp [Finset.mem_erase, hab]
                            have hsum_xm :=
                              (Finset.sum_erase_add (s := (Finset.univ : Finset (Fin 4))) (a := xm)
                                (f := fun a => B (insert1 x a y0))
                                (Finset.mem_univ xm)).symm
                            have hsum_y1 :=
                              (Finset.sum_erase_add (s := (Finset.univ.erase xm)) (a := y1)
                                (f := fun a => B (insert1 x a y0)) hy1_mem).symm
                            have huniv :
                                (∑ a : Fin 4, B (insert1 x a y0))
                                  = (∑ a ∈ allowSet, B (insert1 x a y0)) + B xy := by
                              calc
                                (∑ a : Fin 4, B (insert1 x a y0))
                                    = (∑ a ∈ (Finset.univ.erase xm), B (insert1 x a y0))
                                        + B (insert1 x xm y0) := by
                                          simpa using hsum_xm
                                _ = ((∑ a ∈ allowSet, B (insert1 x a y0))
                                      + B (insert1 x y1 y0))
                                    + B (insert1 x xm y0) := by
                                      rw [hsum_y1]
                                _ = (∑ a ∈ allowSet, B (insert1 x a y0)) + B xy := by
                                      simp [hy1_val, hxm_zero, add_comm]
                            simpa [g, h, y0] using huniv.symm

                          have hsum_succ :
                              (∑ j : Fin n, g j.succ) = ∑ j : Fin n, h j.succ := by
                            refine Fintype.sum_congr _ _ ?_
                            intro j
                            simpa using hsucc j

                          calc
                            (∑ j : Fin (n + 1), g j) + B xy
                                = (g 0 + ∑ j : Fin n, g j.succ) + B xy := by
                                    simp [Fin.sum_univ_succ, g]
                            _ = (g 0 + B xy) + ∑ j : Fin n, g j.succ := by
                                    ac_rfl
                            _ = h 0 + ∑ j : Fin n, h j.succ := by
                                    simp [hzero, hsum_succ]
                            _ = ∑ j : Fin (n + 1), h j := by
                                    exact (Fin.sum_univ_succ (f := h)).symm

                        calc
                          (∑ j : Fin (n + 1), ∑ a ∈ allowSet,
                                B (insert1 x a (erase (n := n) y j))) + B xy
                              = ∑ j : Fin (n + 1), ∑ a : Fin 4,
                                  B (insert1 x a (erase (n := n) y j)) := h_reassemble
                          _ = ∑ j : Fin (n + 1),
                                  2 * choose (m + n + 3) (m + 2) * B x * B (erase (n := n) y j) := by
                                  refine Fintype.sum_congr _ _ ?_
                                  intro j
                                  have hih := ih (m := m + 1) (n := n) (x := x) (y := erase (n := n) y j) hky
                                  -- Only rewrite the binomial coefficient arguments.
                                  have h₁ : (m + 1) + n + 2 = m + n + 3 := by
                                    ac_rfl
                                  have h₂ : (m + 1) + 1 = m + 2 := by
                                    simp [Nat.add_assoc]
                                  simpa [h₁, h₂, Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using hih
                          _ = 2 * choose (m + n + 3) (m + 2) * B x * B y := by
                                  have hmul :
                                      (∑ j : Fin (n + 1),
                                          (2 * choose (m + n + 3) (m + 2) * B x)
                                            * B (erase (n := n) y j))
                                        = (2 * choose (m + n + 3) (m + 2) * B x)
                                            * (∑ j : Fin (n + 1), B (erase (n := n) y j)) := by
                                    simpa using
                                      (Finset.mul_sum (s := (Finset.univ : Finset (Fin (n + 1))))
                                        (f := fun j : Fin (n + 1) => B (erase (n := n) y j))
                                        (a := 2 * choose (m + n + 3) (m + 2) * B x)).symm
                                  calc
                                    (∑ j : Fin (n + 1),
                                          2 * choose (m + n + 3) (m + 2) * B x * B (erase (n := n) y j))
                                        = ∑ j : Fin (n + 1),
                                            (2 * choose (m + n + 3) (m + 2) * B x)
                                              * B (erase (n := n) y j) := by
                                              refine Fintype.sum_congr _ _ ?_
                                              intro j
                                              ac_rfl
                                    _ = (2 * choose (m + n + 3) (m + 2) * B x)
                                          * (∑ j : Fin (n + 1), B (erase (n := n) y j)) := hmul
                                    _ = (2 * choose (m + n + 3) (m + 2) * B x) * B y := by
                                          simpa using
                                            congrArg (fun t => (2 * choose (m + n + 3) (m + 2) * B x) * t) hyB.symm
                                    _ = 2 * choose (m + n + 3) (m + 2) * B x * B y := by
                                          ac_rfl

                      have h_allow :
                          (∑ a ∈ allowSet, B (insert1 x a y))
                            = 2 * (choose (m + n + 3) (m + 1) + choose (m + n + 3) (m + 2)) * B x * B y := by
                        calc
                          (∑ a ∈ allowSet, B (insert1 x a y))
                              = (∑ i : Fin (m + 1), ∑ a ∈ allowSet,
                                    B (insert1 (erase (n := m) x i) a y))
                                  + (allowSet.card * B xy)
                                  + (∑ j : Fin (n + 1), ∑ a ∈ allowSet,
                                    B (insert1 x a (erase (n := n) y j))) := by
                                  simpa using h_allow_split
                          _ = (∑ i : Fin (m + 1), ∑ a ∈ allowSet,
                                    B (insert1 (erase (n := m) x i) a y))
                                  + (B xy + B xy)
                                  + (∑ j : Fin (n + 1), ∑ a ∈ allowSet,
                                    B (insert1 x a (erase (n := n) y j))) := by
                                  simp [hcard, two_mul, add_assoc, add_comm]
                          _ = ((∑ i : Fin (m + 1), ∑ a ∈ allowSet,
                                    B (insert1 (erase (n := m) x i) a y)) + B xy)
                                + ((∑ j : Fin (n + 1), ∑ a ∈ allowSet,
                                    B (insert1 x a (erase (n := n) y j))) + B xy) := by
                                  ac_rfl
                          _ = (2 * choose (m + n + 3) (m + 1) * B x * B y)
                                + (2 * choose (m + n + 3) (m + 2) * B x * B y) := by
                                  simp [hx_total, hy_total]
                          _ = 2 * (choose (m + n + 3) (m + 1) + choose (m + n + 3) (m + 2)) * B x * B y := by
                                  simp [Nat.mul_add, Nat.add_mul, Nat.mul_assoc, add_assoc]

                      have hpascal :
                          choose (m + n + 4) (m + 2)
                            = choose (m + n + 3) (m + 1) + choose (m + n + 3) (m + 2) := by
                        simpa [Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using
                          (Nat.choose_succ_succ' (n := m + n + 3) (k := m + 1))

                      have hchoose :
                          2 * choose (m + n + 4) (m + 2) * B x * B y
                            = 2 * choose ((m + 1) + (n + 1) + 2) ((m + 1) + 1) * B x * B y := by
                        have h₁ : m + n + 4 = (m + 1) + (n + 1) + 2 := by
                          ac_rfl
                        have h₂ : m + 2 = (m + 1) + 1 := by
                          simp [Nat.add_assoc]
                        simp [h₁, h₂]

                      -- Finish.
                      have : (∑ a : Fin 4, B (insert1 x a y))
                          = 2 * choose (m + n + 4) (m + 2) * B x * B y := by
                        calc
                          (∑ a : Fin 4, B (insert1 x a y))
                              = ∑ a ∈ allowSet, B (insert1 x a y) := h_sum
                          _ = 2 * (choose (m + n + 3) (m + 1) + choose (m + n + 3) (m + 2)) * B x * B y := h_allow
                          _ = 2 * choose (m + n + 4) (m + 2) * B x * B y := by
                                simp [hpascal, Nat.mul_assoc]

                      simpa [hchoose] using this

                  · -- `y` not proper: both sides are zero.
                    have hyB0 : B y = 0 := B_eq_zero_of_not_isProper (q := 4) (x := y) (n := n) hy
                    have hterm (a : Fin 4) : B (insert1 x a y) = 0 := by
                      have hnot : ¬ IsProper (insert1 x a y) := by
                        have : ¬ IsProper (append (snoc x a) y) :=
                          Word.not_isProper_append_right_of_not_isProper (q := 4) (x := snoc x a) (y := y) hy
                        simpa [Word.insert1] using this
                      simpa using (B_eq_zero_of_not_isProper (q := 4) (x := insert1 x a y) (n := m + 2 + n) hnot)
                    simp [hyB0, hterm]
                · -- `x` not proper: both sides are zero.
                  have hxB0 : B x = 0 := B_eq_zero_of_not_isProper (q := 4) (x := x) (n := m) hx
                  have hterm (a : Fin 4) : B (insert1 x a y) = 0 := by
                    have hsnoc : ¬ IsProper (snoc x a) := by
                      intro hsnoc
                      exact hx (Word.isProper_of_isProper_snoc (q := 4) (x := x) (a := a) hsnoc)
                    have hnot : ¬ IsProper (insert1 x a y) := by
                      simpa [Word.insert1] using
                        (Word.not_isProper_append_left_of_not_isProper (q := 4) (x := snoc x a) (y := y) hsnoc)
                    simpa using (B_eq_zero_of_not_isProper (q := 4) (x := insert1 x a y) (n := m + 2 + n) hnot)
                  simp [hxB0, hterm]
  exact hk (m + n) (x := x) (y := y) rfl

end Word

end FiniteDependence.Coloring
