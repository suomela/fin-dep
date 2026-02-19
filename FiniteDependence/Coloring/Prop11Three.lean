import FiniteDependence.Coloring.InsertDeletion
import Mathlib.Algebra.BigOperators.Group.Finset.Sigma
import Mathlib.Data.Nat.Choose.Basic

/-!
# Proposition 11, case `q = 3`

This file proves the `q = 3` case of Proposition 11 in Holroyd–Liggett,
*Finitely dependent coloring* (arXiv:1403.2448v4).
-/

open scoped BigOperators

-- The proof of Proposition 11 (q=3) is a large nested induction with many finitary sums.
-- Some intermediate `simp` steps can be expensive, so we raise the heartbeat limit locally.
set_option maxHeartbeats 1000000

namespace FiniteDependence.Coloring

namespace Word

open Nat

private def emptyWord : Word 3 0 := fun i : Fin 0 => i.elim0

private lemma insert2_empty_left {n : ℕ} (a b : Fin 3) (y : Word 3 n) :
    insert2 (q := 3) (m := 0) (n := n) emptyWord a b y
      = Word.cast (q := 3) (Nat.add_comm n 2) (cons a (cons b y)) := by
  classical
  -- Work by splitting indices into the first two positions and the tail.
  ext i
  -- `i : Fin (2 + n)` in the LHS; use `Fin.addCases` with `m = 2`.
  induction i using Fin.addCases with
  | left i =>
      -- `i : Fin 2`.
      cases i using Fin.cases with
      | zero =>
          -- First position.
          have hcast :
              Fin.cast (Nat.add_comm n 2).symm (Fin.castAdd n (0 : Fin 2)) = (0 : Fin (n + 2)) := by
            apply Fin.ext
            simp
          have hl : (snoc (snoc emptyWord a) b) (0 : Fin 2) = a := by
            calc
              (snoc (snoc emptyWord a) b) (0 : Fin 2)
                  = (snoc emptyWord a) (0 : Fin 1) := by
                      simpa using
                        (Word.snoc_castSucc (x := snoc emptyWord a) (a := b) (i := (0 : Fin 1)))
              _ = a := by
                    simpa using (Word.snoc_last (x := emptyWord) (a := a))
          simp [Word.insert2, Word.append, Word.cast, hcast, hl]
      | succ i =>
          -- Second position (`i : Fin 1`).
          have : i = 0 := Subsingleton.elim _ _
          subst this
          have hcast :
              Fin.cast (Nat.add_comm n 2).symm (Fin.castAdd n (1 : Fin 2)) = (0 : Fin (n + 1)).succ := by
            apply Fin.ext
            simp
          have hl : (snoc (snoc emptyWord a) b) (1 : Fin 2) = b := by
            -- Here `1 = Fin.last 1`.
            simpa using (Word.snoc_last (x := snoc emptyWord a) (a := b))
          have hr' : cons a (cons b y) (1 : Fin (n + 2)) = b := by
            have h1 : (1 : Fin (n + 2)) = (0 : Fin (n + 1)).succ := by
              apply Fin.ext
              simp
            calc
              cons a (cons b y) (1 : Fin (n + 2))
                  = cons a (cons b y) ((0 : Fin (n + 1)).succ) := by
                      rw [h1]
              _ = (cons b y) 0 := by simp [Word.cons]
              _ = b := by simp [Word.cons]
          simp [Word.insert2, Word.append, Word.cast, hcast, hl, hr']
  | right j =>
      -- `j : Fin n`, position `2 + j`.
      have hcast :
          Fin.cast (Nat.add_comm n 2).symm (Fin.natAdd 2 j) = j.succ.succ := by
        apply Fin.ext
        simp [Nat.add_comm, Nat.add_left_comm]
      -- Now both sides reduce to `y j`.
      simp [Word.insert2, Word.append, Word.cast, hcast]

private lemma insert2_empty_right {m : ℕ} (x : Word 3 m) (a b : Fin 3) :
    insert2 (q := 3) (m := m) (n := 0) x a b emptyWord = snoc (snoc x a) b := by
  classical
  funext i
  have hempty : (emptyWord : Fin 0 → Fin 3) = Fin.elim0 := rfl
  simp [Word.insert2, Word.append, hempty, Function.comp]

private lemma sum_univ_eq_sum_erase {β : Type*} [AddCommMonoid β] [DecidableEq (Fin 3)]
    (a : Fin 3) (f : Fin 3 → β) (hfa : f a = 0) :
    (∑ x : Fin 3, f x) = ∑ x ∈ (Finset.univ.erase a), f x := by
  have h :=
    (Finset.sum_erase_add (s := (Finset.univ : Finset (Fin 3))) (a := a) (f := f)
      (Finset.mem_univ a)).symm
  simpa [hfa] using h

private lemma sum_univ_eq_sum_erase_erase {β : Type*} [AddCommMonoid β] [DecidableEq (Fin 3)]
    (a b : Fin 3) (hab : b ≠ a) (f : Fin 3 → β) (hfa : f a = 0) (hfb : f b = 0) :
    (∑ x : Fin 3, f x) = ∑ x ∈ ((Finset.univ.erase a).erase b), f x := by
  have hb_mem : b ∈ (Finset.univ.erase a) := by
    simp [Finset.mem_erase, hab]
  have h1 := sum_univ_eq_sum_erase (a := a) (f := f) hfa
  have h2 :=
    (Finset.sum_erase_add (s := (Finset.univ.erase a)) (a := b) (f := f) hb_mem).symm
  calc
    (∑ x : Fin 3, f x)
        = (∑ x ∈ (Finset.univ.erase a), f x) := h1
    _ = (∑ x ∈ ((Finset.univ.erase a).erase b), f x) + f b := by
          simpa using h2
    _ = ∑ x ∈ ((Finset.univ.erase a).erase b), f x := by simp [hfb]

private lemma sum_univ_eq_sum_erase_two {β : Type*} [AddCommMonoid β] [DecidableEq (Fin 3)]
    (a b : Fin 3) (f : Fin 3 → β) (hfa : f a = 0) (hfb : f b = 0) :
    (∑ x : Fin 3, f x) = ∑ x ∈ ((Finset.univ.erase a).erase b), f x := by
  by_cases hab : b = a
  · subst b
    -- Erasing twice is the same as erasing once.
    simpa [Finset.erase_idem] using (sum_univ_eq_sum_erase (a := a) (f := f) hfa)
  · exact sum_univ_eq_sum_erase_erase (a := a) (b := b) (hab := hab) (f := f) hfa hfb

private lemma isProper_insert2_of_isProper {m n : ℕ} (x : Word 3 (m + 1)) (y : Word 3 (n + 1))
    (a b : Fin 3) (hx : IsProper x) (hy : IsProper y)
    (hxa : x (Fin.last m) ≠ a) (hab : a ≠ b) (hby : b ≠ y 0) :
    IsProper (insert2 (q := 3) (m := m + 1) (n := n + 1) x a b y) := by
  have hx1 : IsProper (snoc x a) :=
    (Word.isProper_snoc_iff (x := x) (a := a)).2 ⟨hx, by simpa [Word.snoc] using hxa⟩
  have hx2 : IsProper (snoc (snoc x a) b) :=
    (Word.isProper_snoc_iff (x := snoc x a) (a := b)).2 ⟨hx1, by simpa [Word.snoc] using hab⟩
  have hbd : (snoc (snoc x a) b) (Fin.last (m + 2)) ≠ y 0 := by
    simpa [Word.snoc] using hby
  simpa [Word.insert2, Word.append, Nat.add_assoc, Nat.one_add] using
    (Word.isProper_append_of_isProper (q := 3) (x := snoc (snoc x a) b) (y := y) hx2 hy hbd)

private lemma B_insert2_eq_zero_of_eq_last {m n : ℕ} (x : Word 3 (m + 1)) (b : Fin 3)
    (y : Word 3 (n + 1)) :
    B (insert2 (q := 3) (m := m + 1) (n := n + 1) x (x (Fin.last m)) b y) = 0 := by
  have hsnoc : ¬ IsProper (snoc x (x (Fin.last m))) := Word.not_isProper_snoc_self (x := x)
  have hsnoc2 : ¬ IsProper (snoc (snoc x (x (Fin.last m))) b) := by
    intro h
    exact hsnoc (isProper_of_isProper_snoc (x := snoc x (x (Fin.last m))) (a := b) h)
  have hnot : ¬ IsProper (insert2 (q := 3) (m := m + 1) (n := n + 1) x (x (Fin.last m)) b y) := by
    simpa [Word.insert2, Word.append] using
      (Word.not_isProper_append_left_of_not_isProper (q := 3)
        (x := snoc (snoc x (x (Fin.last m))) b) (y := y) hsnoc2)
  -- The length is `((m+1)+2+n)+1`.
  simpa [Word.insert2, Nat.add_assoc, Nat.one_add] using
    (B_eq_zero_of_not_isProper (q := 3)
      (x := insert2 (q := 3) (m := m + 1) (n := n + 1) x (x (Fin.last m)) b y)
      (n := (m + 1) + 2 + n) hnot)

private lemma B_insert2_eq_zero_of_eq_mid {m n : ℕ} (x : Word 3 (m + 1)) (a : Fin 3)
    (y : Word 3 (n + 1)) :
    B (insert2 (q := 3) (m := m + 1) (n := n + 1) x a a y) = 0 := by
  have hsnoc : ¬ IsProper (snoc (snoc x a) a) := by
    -- `snoc (snoc x a) a` repeats the last letter of `snoc x a`, which is `a`.
    simpa [Word.snoc] using (Word.not_isProper_snoc_self (x := snoc x a))
  have hnot : ¬ IsProper (insert2 (q := 3) (m := m + 1) (n := n + 1) x a a y) := by
    simpa [Word.insert2, Word.append] using
      (Word.not_isProper_append_left_of_not_isProper (q := 3)
        (x := snoc (snoc x a) a) (y := y) hsnoc)
  simpa [Word.insert2, Nat.add_assoc, Nat.one_add] using
    (B_eq_zero_of_not_isProper (q := 3)
      (x := insert2 (q := 3) (m := m + 1) (n := n + 1) x a a y)
      (n := (m + 1) + 2 + n) hnot)

private lemma B_insert2_eq_zero_of_eq_first {m n : ℕ} (x : Word 3 (m + 1)) (a : Fin 3)
    (y : Word 3 (n + 1)) :
    B (insert2 (q := 3) (m := m + 1) (n := n + 1) x a (y 0) y) = 0 := by
  have hbd : (snoc (snoc x a) (y 0)) (Fin.last (m + 2)) = y 0 := by
    simp [Word.snoc]
  have hnot : ¬ IsProper (insert2 (q := 3) (m := m + 1) (n := n + 1) x a (y 0) y) := by
    have : ¬ IsProper (append (snoc (snoc x a) (y 0)) y) :=
      Word.not_isProper_append_of_eq_boundary (q := 3) (x := snoc (snoc x a) (y 0)) (y := y)
        (by simp [hbd])
    simpa [Word.insert2, Word.append] using this
  simpa [Word.insert2, Nat.add_assoc, Nat.one_add] using
    (B_eq_zero_of_not_isProper (q := 3)
      (x := insert2 (q := 3) (m := m + 1) (n := n + 1) x a (y 0) y)
      (n := (m + 1) + 2 + n) hnot)

private lemma insert2_erase_last_eq_insert1 {m n : ℕ} (x : Word 3 (m + 1)) (b : Fin 3) (y : Word 3 (n + 1)) :
    insert2 (q := 3) (m := m) (n := n + 1) (erase (n := m) x (Fin.last m)) (x (Fin.last m)) b y
      = insert1 (q := 3) (m := m + 1) (n := n + 1) x b y := by
  have hx : snoc (erase (n := m) x (Fin.last m)) (x (Fin.last m)) = x := by
    simp
  -- Rewrite `snoc (erase ...) (x last)` to `x`, then unfold.
  simp [Word.insert2, Word.insert1, Word.append, hx]

private lemma B_insert1_eq_B_insert2_erase_zero {m n : ℕ} (x : Word 3 (m + 1)) (a : Fin 3)
    (y : Word 3 (n + 1)) :
    B (insert1 (q := 3) (m := m + 1) (n := n + 1) x a y)
      = B (insert2 (q := 3) (m := m + 1) (n := n) x a (y 0) (erase (n := n) y 0)) := by
  -- `insert1 x a y` and `insert2 x a (y 0) (erase y 0)` are equal up to a cast of lengths;
  -- remove the cast using `B_cast`.
  classical
  have hy : cons (y 0) (erase (n := n) y 0) = y := by
    ext i
    cases i using Fin.cases with
    | zero => simp [Word.cons]
    | succ i =>
        simp [Word.cons, Word.erase]
  -- Use `Fin.append_right_cons` and rewrite `cons (y 0) (erase y 0)` to `y`.
  have happ :=
    Fin.append_right_cons (xs := snoc x a) (y := y 0) (ys := erase (n := n) y 0)
  have happ' :
      append (q := 3) (m := (m + 1) + 1) (n := n + 1) (snoc x a) y
        = append (q := 3) (m := (m + 1) + 2) (n := n) (snoc (snoc x a) (y 0)) (erase (n := n) y 0)
            ∘ Fin.cast (Nat.succ_add_eq_add_succ ((m + 1) + 1) n).symm := by
    have happ1 :
        append (q := 3) (m := (m + 1) + 1) (n := n + 1) (snoc x a) (cons (y 0) (erase (n := n) y 0))
          = append (q := 3) (m := (m + 1) + 2) (n := n) (snoc (snoc x a) (y 0)) (erase (n := n) y 0)
              ∘ Fin.cast (Nat.succ_add_eq_add_succ ((m + 1) + 1) n).symm := by
      simpa [Word.append, Word.snoc, Word.cons] using happ
    simpa [hy] using happ1
  have heq :
      insert1 (q := 3) (m := m + 1) (n := n + 1) x a y
        = Word.cast (q := 3) (Nat.succ_add_eq_add_succ ((m + 1) + 1) n)
            (insert2 (q := 3) (m := m + 1) (n := n) x a (y 0) (erase (n := n) y 0)) := by
    funext i
    have hi := congrArg (fun f => f i) happ'
    -- Unfold insert operations, and rewrite the `cons` decomposition of `y`.
    simpa [Word.insert1, Word.insert2, Word.append, Word.cast, Function.comp, hy, Nat.add_assoc, Nat.one_add] using hi
  -- Apply `B` and remove the cast.
  simpa [B_cast] using congrArg (fun w => B (q := 3) w) heq

/-- Proposition 11 (q=3): summing `B` over the two inserted letters. -/
theorem sum_B_insert2_three :
    ∀ {m n : ℕ} (x : Word 3 m) (y : Word 3 n),
      (∑ a : Fin 3, ∑ b : Fin 3, B (insert2 (q := 3) (m := m) (n := n) x a b y))
        = 2 * choose (m + n + 4) (m + 2) * B x * B y := by
  classical
  intro m n x y
  -- Induction on `k = m + n`.
  have hk :
      ∀ k : ℕ, ∀ {m n : ℕ} (x : Word 3 m) (y : Word 3 n),
        m + n = k →
          (∑ a : Fin 3, ∑ b : Fin 3, B (insert2 (q := 3) (m := m) (n := n) x a b y))
            = 2 * choose (m + n + 4) (m + 2) * B x * B y := by
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
        -- Base case `m = n = 0`: `insert2` produces a word of length `2`.
        -- Such a word is proper iff its two letters are different; in that case `B = 2`, otherwise `B = 0`.
        have hB_len1 : ∀ z : Word 3 1, B z = 1 := by
          intro z
          simp [B, IsProper]
        have hB_insert2 :
            ∀ a b : Fin 3,
              B (insert2 (q := 3) (m := 0) (n := 0) emptyWord a b emptyWord)
                = if a = b then 0 else 2 := by
          intro a b
          by_cases hab : a = b
          · subst hab
            simp [insert2_empty_left, B, IsProper]
          · simp [insert2_empty_left, B, IsProper, hab]
        have hsum :
            (∑ a : Fin 3, ∑ b : Fin 3, if a = b then (0 : ℕ) else 2) = 12 := by
          simp [Fin.sum_univ_three]
        have hLHS :
            (∑ a : Fin 3, ∑ b : Fin 3,
                B (insert2 (q := 3) (m := 0) (n := 0) emptyWord a b emptyWord)) = 12 := by
          calc
            (∑ a : Fin 3, ∑ b : Fin 3,
                  B (insert2 (q := 3) (m := 0) (n := 0) emptyWord a b emptyWord))
                = ∑ a : Fin 3, ∑ b : Fin 3, if a = b then (0 : ℕ) else 2 := by
                    simp [hB_insert2]
            _ = 12 := hsum
        -- Now compare with the closed form: `2 * choose 4 2 * 1 * 1 = 12`.
        have hRHS :
            2 * choose (0 + 0 + 4) (0 + 2) * B emptyWord * B emptyWord = 12 := by
          -- Reduce to a concrete numeral identity.
          simpa [B, IsProper] using (by decide : (2 * choose 4 2 : ℕ) = 12)
        exact hLHS.trans hRHS.symm
    | succ k ih =>
        intro m n x y hmn
        cases m with
        | zero =>
            -- `m = 0`: reduce to Proposition 10 twice at the left end.
            have hx0 : x = emptyWord := Subsingleton.elim _ _
            subst hx0
            -- Remove casts using `B_cast`.
            have hrewrite :
                (∑ a : Fin 3, ∑ b : Fin 3,
                    B (insert2 (q := 3) (m := 0) (n := n) emptyWord a b y))
                  = ∑ a : Fin 3, ∑ b : Fin 3, B (cons a (cons b y)) := by
              refine Fintype.sum_congr _ _ ?_
              intro a
              refine Fintype.sum_congr _ _ ?_
              intro b
              have := congrArg (fun w => B (q := 3) w) (insert2_empty_left (a := a) (b := b) (y := y))
              simpa [B_cast] using this
            -- Evaluate by applying Proposition 10 twice.
            have hinner : ∀ b : Fin 3, (∑ a : Fin 3, B (cons a (cons b y))) = (n + 4) * B (cons b y) := by
              intro b
              -- `cons b y` has length `n + 1`.
              simpa [Nat.mul_comm, Nat.mul_left_comm, Nat.mul_assoc, Nat.add_assoc, Nat.one_add] using
                (sum_B_cons (q := 3) (by decide : 2 ≤ (3 : ℕ)) (x := cons b y))
            have hsum_b :
                (∑ b : Fin 3, (n + 4) * B (cons b y))
                  = (n + 4) * (∑ b : Fin 3, B (cons b y)) := by
              simpa using
                (Finset.mul_sum (s := (Finset.univ : Finset (Fin 3)))
                  (f := fun b : Fin 3 => B (cons b y)) (a := n + 4)).symm
            have hchoose :
                (n + 4) * (n + 3) = 2 * choose (n + 4) 2 := by
              -- Use `(n+4) * choose (n+3) 1 = choose (n+4) 2 * 2`.
              have h := Nat.add_one_mul_choose_eq (n := n + 3) (k := 1)
              have h' : (n + 4) * (n + 3) = choose (n + 4) 2 * 2 := by
                simpa using h
              -- Turn `choose _ _ * 2` into `2 * choose _ _`.
              calc
                (n + 4) * (n + 3) = choose (n + 4) 2 * 2 := h'
                _ = 2 * choose (n + 4) 2 := by ac_rfl
            calc
              (∑ a : Fin 3, ∑ b : Fin 3,
                  B (insert2 (q := 3) (m := 0) (n := n) emptyWord a b y))
                  = ∑ a : Fin 3, ∑ b : Fin 3, B (cons a (cons b y)) := hrewrite
              _ = (n + 4) * ((n + 3) * B y) := by
                    -- Sum over `a`, then over `b`.
                    have : (∑ a : Fin 3, ∑ b : Fin 3, B (cons a (cons b y)))
                        = ∑ b : Fin 3, (∑ a : Fin 3, B (cons a (cons b y))) := by
                          simpa using
                            (Finset.sum_comm (s := (Finset.univ : Finset (Fin 3)))
                              (t := (Finset.univ : Finset (Fin 3)))
                              (f := fun a b => B (cons a (cons b y))))
                    -- Replace the inner sum and then evaluate the outer one.
                    calc
                        (∑ a : Fin 3, ∑ b : Fin 3, B (cons a (cons b y))) =
                            ∑ b : Fin 3, (∑ a : Fin 3, B (cons a (cons b y))) := this
                        _ = ∑ b : Fin 3, (n + 4) * B (cons b y) := by
                              refine Fintype.sum_congr _ _ ?_
                              intro b
                              simp [hinner b]
                        _ = (n + 4) * (∑ b : Fin 3, B (cons b y)) := hsum_b
                        _ = (n + 4) * ((n + 3) * B y) := by
                              -- Apply Proposition 10 once more.
                              simp [sum_B_cons (q := 3) (by decide : 2 ≤ (3 : ℕ)) (x := y),
                                Nat.mul_left_comm]
              _ = 2 * choose (0 + n + 4) (0 + 2) * B (q := 3) emptyWord * B y := by
                    -- Use `hchoose : (n+4)*(n+3)=2*choose(n+4)2`.
                    have :
                        (n + 4) * ((n + 3) * B y) = 2 * choose (n + 4) 2 * B y := by
                      calc
                        (n + 4) * ((n + 3) * B y) = ((n + 4) * (n + 3)) * B y := by ac_rfl
                        _ = (2 * choose (n + 4) 2) * B y := by simp [hchoose]
                        _ = 2 * choose (n + 4) 2 * B y := by ac_rfl
                    -- Rewrite the target RHS and finish by associativity.
                    simp [this]
        | succ m =>
            cases n with
            | zero =>
                -- `n = 0`: reduce to Proposition 10 twice at the right end.
                have hy0 : y = emptyWord := Subsingleton.elim _ _
                subst hy0
                have hrewrite :
                    (∑ a : Fin 3, ∑ b : Fin 3, B (insert2 (q := 3) (m := m + 1) (n := 0) x a b emptyWord))
                      = ∑ a : Fin 3, ∑ b : Fin 3, B (snoc (snoc x a) b) := by
                  refine Fintype.sum_congr _ _ ?_
                  intro a
                  refine Fintype.sum_congr _ _ ?_
                  intro b
                  simp [insert2_empty_right (x := x) (a := a) (b := b)]
                have hinner : ∀ a : Fin 3, (∑ b : Fin 3, B (snoc (snoc x a) b)) = (m + 5) * B (snoc x a) := by
                  intro a
                  simpa [Nat.mul_add, Nat.add_assoc] using
                    (sum_B_snoc (q := 3) (by decide : 2 ≤ (3 : ℕ)) (x := snoc x a))
                have hsum_a :
                    (∑ a : Fin 3, (m + 5) * B (snoc x a))
                      = (m + 5) * (∑ a : Fin 3, B (snoc x a)) := by
                  simpa using
                    (Finset.mul_sum (s := (Finset.univ : Finset (Fin 3)))
                      (f := fun a : Fin 3 => B (snoc x a)) (a := m + 5)).symm
                have hchoose :
                    (m + 5) * (m + 4) = 2 * choose (m + 5) 2 := by
                  have h := Nat.add_one_mul_choose_eq (n := m + 4) (k := 1)
                  have h' : (m + 5) * (m + 4) = choose (m + 5) 2 * 2 := by
                    simpa using h
                  calc
                    (m + 5) * (m + 4) = choose (m + 5) 2 * 2 := h'
                    _ = 2 * choose (m + 5) 2 := by ac_rfl
                calc
                  (∑ a : Fin 3, ∑ b : Fin 3, B (insert2 (q := 3) (m := m + 1) (n := 0) x a b emptyWord))
                      = ∑ a : Fin 3, ∑ b : Fin 3, B (snoc (snoc x a) b) := hrewrite
                  _ = (m + 5) * ((m + 4) * B x) := by
                        calc
                          (∑ a : Fin 3, ∑ b : Fin 3, B (snoc (snoc x a) b))
                              = ∑ a : Fin 3, (∑ b : Fin 3, B (snoc (snoc x a) b)) := rfl
                          _ = ∑ a : Fin 3, (m + 5) * B (snoc x a) := by
                                refine Fintype.sum_congr _ _ ?_
                                intro a
                                simp [hinner a]
                          _ = (m + 5) * (∑ a : Fin 3, B (snoc x a)) := hsum_a
                          _ = (m + 5) * ((m + 4) * B x) := by
                                -- Apply Proposition 10 once more.
                                have h := sum_B_snoc (q := 3) (by decide : 2 ≤ (3 : ℕ)) (x := x)
                                -- `x` has length `m+1`, so the coefficient is `m+4`.
                                simpa [Nat.mul_add, Nat.add_assoc, Nat.mul_assoc] using congrArg (fun t => (m + 5) * t) h
                  _ = 2 * choose ((m + 1) + 0 + 4) ((m + 1) + 2) * B x * B (q := 3) emptyWord := by
                        -- Rewrite `choose (m+5) (m+3)` as `choose (m+5) 2`, then use `hchoose`.
                        have hk : m + 3 ≤ m + 5 := by omega
                        have hsub : (m + 5) - (m + 3) = 2 := by omega
                        have hsymm :
                            choose (m + 5) (m + 3) = choose (m + 5) 2 := by
                          simpa [hsub] using (Nat.choose_symm (n := m + 5) (k := m + 3) hk).symm
                        have :
                            (m + 5) * ((m + 4) * B x) = 2 * choose (m + 5) 2 * B x := by
                          calc
                            (m + 5) * ((m + 4) * B x) = ((m + 5) * (m + 4)) * B x := by ac_rfl
                            _ = (2 * choose (m + 5) 2) * B x := by simp [hchoose]
                            _ = 2 * choose (m + 5) 2 * B x := by ac_rfl
                        -- Finish by rewriting the goal.
                        simp [hsymm, this]
            | succ n =>
                -- Main case: both `x` and `y` are nonempty.
                by_cases hx : IsProper x
                · by_cases hy : IsProper y
                  · -- Proper case: use `B_insert2_eq` and the induction hypothesis.
                    let xm : Fin 3 := x (Fin.last m)
                    let y1 : Fin 3 := y 0
                    let allowB : Finset (Fin 3) := Finset.univ.erase y1
                    let allowA : Fin 3 → Finset (Fin 3) := fun b => (Finset.univ.erase xm).erase b

                    have hxB : B x = ∑ i : Fin (m + 1), B (erase (n := m) x i) := by
                      simpa using
                        (B_eq_sum_erase_of_isProper (q := 3) (x := x) (n := m) hx)
                    have hyB : B y = ∑ j : Fin (n + 1), B (erase (n := n) y j) := by
                      simpa using
                        (B_eq_sum_erase_of_isProper (q := 3) (x := y) (n := n) hy)

                    -- Swap the outer sums to work with `b` first.
                    have hswap :
                        (∑ a : Fin 3, ∑ b : Fin 3, B (insert2 (q := 3) (m := m + 1) (n := n + 1) x a b y))
                          = ∑ b : Fin 3, ∑ a : Fin 3, B (insert2 (q := 3) (m := m + 1) (n := n + 1) x a b y) := by
                      simpa using
                        (Finset.sum_comm (s := (Finset.univ : Finset (Fin 3)))
                          (t := (Finset.univ : Finset (Fin 3)))
                          (f := fun a b =>
                            B (insert2 (q := 3) (m := m + 1) (n := n + 1) x a b y)))

                    -- Restrict `b` to `allowB` (since `b = y1` always gives `B = 0`).
                    have h_outer :
                        (∑ b : Fin 3, ∑ a : Fin 3, B (insert2 (q := 3) (m := m + 1) (n := n + 1) x a b y))
                          = ∑ b ∈ allowB, ∑ a : Fin 3,
                              B (insert2 (q := 3) (m := m + 1) (n := n + 1) x a b y) := by
                      have h0 :
                          (∑ a : Fin 3, B (insert2 (q := 3) (m := m + 1) (n := n + 1) x a y1 y)) = 0 := by
                        have : ∀ a : Fin 3,
                            B (insert2 (q := 3) (m := m + 1) (n := n + 1) x a y1 y) = 0 := by
                          intro a
                          simpa [y1] using
                            (B_insert2_eq_zero_of_eq_first (m := m) (n := n) (x := x) (a := a) (y := y))
                        simp [this]
                      simpa [allowB, y1] using
                        (sum_univ_eq_sum_erase (a := y1)
                          (f := fun b : Fin 3 =>
                            ∑ a : Fin 3, B (insert2 (q := 3) (m := m + 1) (n := n + 1) x a b y))
                          (by simp [h0]))

                    -- Restrict `a` to `allowA b` for each `b ∈ allowB`.
                    have h_inner (b : Fin 3) (hb : b ∈ allowB) :
                        (∑ a : Fin 3, B (insert2 (q := 3) (m := m + 1) (n := n + 1) x a b y))
                          = ∑ a ∈ allowA b, B (insert2 (q := 3) (m := m + 1) (n := n + 1) x a b y) := by
                      have h0a :
                          B (insert2 (q := 3) (m := m + 1) (n := n + 1) x xm b y) = 0 := by
                        simpa [xm] using (B_insert2_eq_zero_of_eq_last (m := m) (n := n) (x := x) (b := b) (y := y))
                      have h0b :
                          B (insert2 (q := 3) (m := m + 1) (n := n + 1) x b b y) = 0 := by
                        simpa using (B_insert2_eq_zero_of_eq_mid (m := m) (n := n) (x := x) (a := b) (y := y))
                      simpa [allowA, xm] using
                        (sum_univ_eq_sum_erase_two (a := xm) (b := b)
                          (f := fun a : Fin 3 =>
                            B (insert2 (q := 3) (m := m + 1) (n := n + 1) x a b y))
                          (by simp [h0a]) (by simp [h0b]))

                    have h_restrict :
                        (∑ a : Fin 3, ∑ b : Fin 3, B (insert2 (q := 3) (m := m + 1) (n := n + 1) x a b y))
                          = ∑ b ∈ allowB, ∑ a ∈ allowA b,
                              B (insert2 (q := 3) (m := m + 1) (n := n + 1) x a b y) := by
                      calc
                        (∑ a : Fin 3, ∑ b : Fin 3, B (insert2 (q := 3) (m := m + 1) (n := n + 1) x a b y))
                            = ∑ b : Fin 3, ∑ a : Fin 3, B (insert2 (q := 3) (m := m + 1) (n := n + 1) x a b y) := hswap
                        _ = ∑ b ∈ allowB, ∑ a : Fin 3,
                              B (insert2 (q := 3) (m := m + 1) (n := n + 1) x a b y) := h_outer
                        _ = ∑ b ∈ allowB, ∑ a ∈ allowA b,
                              B (insert2 (q := 3) (m := m + 1) (n := n + 1) x a b y) := by
                              refine Finset.sum_congr rfl ?_
                              intro b hb
                              simpa using h_inner b hb

                    -- Expand each `B (insert2 x a b y)` using `B_insert2_eq`.
                    have h_expand (b : Fin 3) (hb : b ∈ allowB) (a : Fin 3) (ha : a ∈ allowA b) :
                        B (insert2 (q := 3) (m := m + 1) (n := n + 1) x a b y)
                          = (∑ i : Fin (m + 1),
                                B (insert2 (q := 3) (m := m) (n := n + 1) (erase (n := m) x i) a b y))
                              + B (insert1 (q := 3) (m := m + 1) (n := n + 1) x b y)
                              + B (insert1 (q := 3) (m := m + 1) (n := n + 1) x a y)
                              + ∑ j : Fin (n + 1),
                                  B (insert2 (q := 3) (m := m + 1) (n := n) x a b (erase (n := n) y j)) := by
                      have hb_ne : b ≠ y1 := (Finset.mem_erase.mp hb).1
                      have ha_ne_b : a ≠ b := (Finset.mem_erase.mp ha).1
                      have ha_ne_xm : a ≠ xm := (Finset.mem_erase.mp (Finset.mem_erase.mp ha).2).1
                      have hproper :
                          IsProper (insert2 (q := 3) (m := m + 1) (n := n + 1) x a b y) :=
                        isProper_insert2_of_isProper (m := m) (n := n) (x := x) (y := y) (a := a) (b := b)
                          hx hy (by simpa [xm] using ha_ne_xm.symm) ha_ne_b (by simpa [y1] using hb_ne)
                      have :=
                        B_insert2_eq (q := 3) (m := m) (n := n) (x := x) (a := a) (b := b) (y := y) hproper
                      simpa [Nat.add_assoc, Nat.one_add, add_assoc] using this

                    -- Helper equalities to apply the induction hypothesis (`ih`).
                    have hkx : m + (n + 1) = k := by
                      have h₁ : m + 1 + (n + 1) = m + (n + 1) + 1 := by
                        ac_rfl
                      have h' : (m + (n + 1)) + 1 = k + 1 := h₁.symm.trans hmn
                      exact Nat.add_right_cancel h'
                    have hky : (m + 1) + n = k := by
                      have h₁ : m + 1 + (n + 1) = (m + 1) + n + 1 := by
                        ac_rfl
                      have h' : ((m + 1) + n) + 1 = k + 1 := h₁.symm.trans hmn
                      exact Nat.add_right_cancel h'

                    -- Rewrite the restricted sum using the expansion.
                    have h_main :
                        (∑ b ∈ allowB, ∑ a ∈ allowA b,
                            B (insert2 (q := 3) (m := m + 1) (n := n + 1) x a b y))
                          =
                          ∑ b ∈ allowB, ∑ a ∈ allowA b,
                              ((∑ i : Fin (m + 1),
                                    B (insert2 (q := 3) (m := m) (n := n + 1) (erase (n := m) x i) a b y))
                                + B (insert1 (q := 3) (m := m + 1) (n := n + 1) x b y)
                                + B (insert1 (q := 3) (m := m + 1) (n := n + 1) x a y)
                                + ∑ j : Fin (n + 1),
                                    B (insert2 (q := 3) (m := m + 1) (n := n) x a b (erase (n := n) y j))) := by
                      refine Finset.sum_congr rfl ?_
                      intro b hb
                      refine Finset.sum_congr rfl ?_
                      intro a ha
                      simp [h_expand b hb a ha]

                    -- Name the four contributions, matching equation (6) in the paper.
                    let Si : Nat :=
                      ∑ b ∈ allowB, ∑ a ∈ allowA b, ∑ i : Fin (m + 1),
                        B (insert2 (q := 3) (m := m) (n := n + 1) (erase (n := m) x i) a b y)
                    let Sb : Nat :=
                      ∑ b ∈ allowB, ∑ a ∈ allowA b,
                        B (insert1 (q := 3) (m := m + 1) (n := n + 1) x b y)
                    let Sa : Nat :=
                      ∑ b ∈ allowB, ∑ a ∈ allowA b,
                        B (insert1 (q := 3) (m := m + 1) (n := n + 1) x a y)
                    let Sj : Nat :=
                      ∑ b ∈ allowB, ∑ a ∈ allowA b, ∑ j : Fin (n + 1),
                        B (insert2 (q := 3) (m := m + 1) (n := n) x a b (erase (n := n) y j))

                    have hsplit :
                        (∑ b ∈ allowB, ∑ a ∈ allowA b,
                            ((∑ i : Fin (m + 1),
                                    B (insert2 (q := 3) (m := m) (n := n + 1) (erase (n := m) x i) a b y))
                                + B (insert1 (q := 3) (m := m + 1) (n := n + 1) x b y)
                                + B (insert1 (q := 3) (m := m + 1) (n := n + 1) x a y)
                                + ∑ j : Fin (n + 1),
                                    B (insert2 (q := 3) (m := m + 1) (n := n) x a b (erase (n := n) y j))))
                          = Si + Sb + Sa + Sj := by
                      -- Distribute sums, keeping the natural order (no commutativity needed).
                      simp [Si, Sb, Sa, Sj, Finset.sum_add_distrib, add_assoc]

                    -- Simplify `Sb`: it counts each `b` once.
                    have hSb :
                        Sb = ∑ b ∈ allowB, B (insert1 (q := 3) (m := m + 1) (n := n + 1) x b y) := by
                      -- For each `b`, the inner sum over `a` is either `1` or `2`, but the `b = xm` case has `B = 0`.
                      have hb_term (b : Fin 3) (hb : b ∈ allowB) :
                          (∑ a ∈ allowA b, B (insert1 (q := 3) (m := m + 1) (n := n + 1) x b y))
                            = B (insert1 (q := 3) (m := m + 1) (n := n + 1) x b y) := by
                        by_cases hbx : b = xm
                        · subst hbx
                          -- Repeats the last letter of `x`, so `B = 0`.
                          have h0 : B (insert1 (q := 3) (m := m + 1) (n := n + 1) x xm y) = 0 := by
                            -- Not proper since `snoc x xm` is not proper.
                            have hsnoc : ¬ IsProper (snoc x xm) := by
                              simpa [xm] using (Word.not_isProper_snoc_self (x := x))
                            have hnot : ¬ IsProper (insert1 (q := 3) (m := m + 1) (n := n + 1) x xm y) := by
                              simpa [Word.insert1, Word.append] using
                                (Word.not_isProper_append_left_of_not_isProper (q := 3) (x := snoc x xm) (y := y) hsnoc)
                            -- Align lengths using a cast, then apply `B_eq_zero_of_not_isProper`.
                            have hlen : (m + 1) + 1 + (n + 1) = ((m + 1) + n + 1) + 1 := by
                              ac_rfl
                            have hnot' :
                                ¬ IsProper (Word.cast (q := 3) hlen
                                  (insert1 (q := 3) (m := m + 1) (n := n + 1) x xm y)) := by
                              simpa [Word.isProper_cast_iff] using hnot
                            have hB0 :
                                B (Word.cast (q := 3) hlen
                                  (insert1 (q := 3) (m := m + 1) (n := n + 1) x xm y)) = 0 := by
                              simpa using
                                (B_eq_zero_of_not_isProper (q := 3)
                                  (x := Word.cast (q := 3) hlen
                                    (insert1 (q := 3) (m := m + 1) (n := n + 1) x xm y))
                                  (n := (m + 1) + n + 1) hnot')
                            simpa [B_cast] using hB0
                          -- Inner sum is `card * 0 = 0`.
                          simp [allowA, xm, h0]
                        · have hcard : (allowA b).card = 1 := by
                            -- Remove two distinct elements from `Fin 3`.
                            have hb_mem : b ∈ (Finset.univ.erase xm) := by
                              simp [Finset.mem_erase, hbx]
                            have := Finset.card_erase_of_mem (s := (Finset.univ.erase xm)) hb_mem
                            -- `Finset.univ.erase xm` has card `2`.
                            have h2 : (Finset.univ.erase xm).card = 2 := by
                              -- `Fin 3` has 3 elements.
                              simp
                            -- Hence erasing one more element gives card `1`.
                            simpa [allowA, h2] using this
                          -- Now the inner sum is `1 * B = B`.
                          simp [hcard]
                      -- Sum over `b`.
                      simpa [Sb] using
                        (Finset.sum_congr rfl (fun b hb => hb_term b hb))

                    -- Simplify `Sa`: it counts each `a` once (the `a = y1` contribution is zero anyway).
                    have hSa :
                        Sa = ∑ a ∈ (Finset.univ.erase xm),
                            B (insert1 (q := 3) (m := m + 1) (n := n + 1) x a y) := by
                      -- Swap the dependent sums using `Finset.sum_comm'`.
                      have hswapSa :
                          Sa =
                            ∑ a ∈ (Finset.univ.erase xm), ∑ b ∈ (Finset.univ.erase y1).erase a,
                              B (insert1 (q := 3) (m := m + 1) (n := n + 1) x a y) := by
                        -- `b ∈ allowB` and `a ∈ allowA b` iff `a ∈ univ.erase xm` and `b ∈ (univ.erase y1).erase a`.
                        have hmem :
                            ∀ b a : Fin 3,
                              b ∈ allowB ∧ a ∈ allowA b ↔ b ∈ ((Finset.univ.erase y1).erase a) ∧ a ∈ (Finset.univ.erase xm) := by
                          intro b a
                          constructor
                          · rintro ⟨hb, ha⟩
                            have hb_ne_y1 : b ≠ y1 := (Finset.mem_erase.mp hb).1
                            have ha_ne_b : a ≠ b := (Finset.mem_erase.mp ha).1
                            have ha_mem_univ_erase_xm : a ∈ (Finset.univ.erase xm) := (Finset.mem_erase.mp ha).2
                            refine ⟨?_, ha_mem_univ_erase_xm⟩
                            refine Finset.mem_erase.mpr ?_
                            refine ⟨ha_ne_b.symm, ?_⟩
                            exact Finset.mem_erase.mpr ⟨hb_ne_y1, Finset.mem_univ b⟩
                          · rintro ⟨hb, ha⟩
                            have hb_ne_a : b ≠ a := (Finset.mem_erase.mp hb).1
                            have hb_mem_univ_erase_y1 : b ∈ (Finset.univ.erase y1) := (Finset.mem_erase.mp hb).2
                            have hb_ne_y1 : b ≠ y1 := (Finset.mem_erase.mp hb_mem_univ_erase_y1).1
                            refine ⟨?_, ?_⟩
                            · exact Finset.mem_erase.mpr ⟨hb_ne_y1, Finset.mem_univ b⟩
                            · exact Finset.mem_erase.mpr ⟨hb_ne_a.symm, ha⟩
                        simpa [Sa] using
                          (Finset.sum_comm' (s := allowB) (t := allowA)
                            (t' := (Finset.univ.erase xm)) (s' := fun a => (Finset.univ.erase y1).erase a)
                            (f := fun b a => B (insert1 (q := 3) (m := m + 1) (n := n + 1) x a y)) hmem)
                      -- Now the inner sum is a constant; it is `1 * B`, except when `a = y1` where the term is `0`.
                      have h0first :
                          B (insert1 (q := 3) (m := m + 1) (n := n + 1) x y1 y) = 0 := by
                        -- Boundary failure between the inserted letter `y1` and the first letter of `y`.
                        have hnot : ¬ IsProper (insert1 (q := 3) (m := m + 1) (n := n + 1) x y1 y) := by
                          have hbd : (snoc x y1) (Fin.last (m + 1)) = y 0 := by
                            simp [y1, Word.snoc]
                          have : ¬ IsProper (append (snoc x y1) y) :=
                            Word.not_isProper_append_of_eq_boundary (q := 3) (x := snoc x y1) (y := y)
                              (by simpa using hbd)
                          simpa [Word.insert1, Word.append] using this
                        -- Align lengths using a cast, then apply `B_eq_zero_of_not_isProper`.
                        have hlen : (m + 1) + 1 + (n + 1) = (m + n + 2) + 1 := by
                          ac_rfl
                        have hnot' :
                            ¬ IsProper (Word.cast (q := 3) hlen
                              (insert1 (q := 3) (m := m + 1) (n := n + 1) x y1 y)) := by
                          simpa [Word.isProper_cast_iff] using hnot
                        have hB0 :
                            B (Word.cast (q := 3) hlen
                              (insert1 (q := 3) (m := m + 1) (n := n + 1) x y1 y)) = 0 := by
                          simpa using
                            (B_eq_zero_of_not_isProper (q := 3)
                              (x := Word.cast (q := 3) hlen
                                (insert1 (q := 3) (m := m + 1) (n := n + 1) x y1 y))
                              (n := m + n + 2) hnot')
                        simpa [B_cast] using hB0
                      -- Evaluate the swapped form.
                      calc
                        Sa = ∑ a ∈ (Finset.univ.erase xm), ∑ b ∈ (Finset.univ.erase y1).erase a,
                              B (insert1 (q := 3) (m := m + 1) (n := n + 1) x a y) := hswapSa
                        _ = ∑ a ∈ (Finset.univ.erase xm),
                              B (insert1 (q := 3) (m := m + 1) (n := n + 1) x a y) := by
                              refine Finset.sum_congr rfl ?_
                              intro a ha
                              by_cases hay : a = y1
                              · subst hay
                                -- The term is zero, so the sum is zero.
                                simp [h0first]
                              · -- The inner finset has card `1`, so the sum of a constant is that constant.
                                have ha_mem : a ∈ (Finset.univ.erase y1) := by
                                  simp [Finset.mem_erase, hay]
                                have hcard :=
                                  Finset.card_erase_of_mem (s := (Finset.univ.erase y1)) ha_mem
                                have h2 : (Finset.univ.erase y1).card = 2 := by
                                  simp
                                have : ((Finset.univ.erase y1).erase a).card = 1 := by
                                  simpa [h2] using hcard
                                simp [this]

                    -- Abbreviations used in the inductive computation (cf. the end of the paper proof).
                    let z : Word 3 m := erase (n := m) x (Fin.last m)
                    let y0 : Word 3 n := erase (n := n) y 0
                    let c1 : Nat := 2 * choose (m + n + 5) (m + 2)
                    let c2 : Nat := 2 * choose (m + n + 5) (m + 3)

                    -- Split `Si` into `i < last` and `i = last`.
                    let Si_cast : Nat :=
                      ∑ b ∈ allowB, ∑ a ∈ allowA b, ∑ i : Fin m,
                        B (insert2 (q := 3) (m := m) (n := n + 1) (erase (n := m) x i.castSucc) a b y)
                    let Si_last : Nat :=
                      ∑ b ∈ allowB, ∑ a ∈ allowA b,
                        B (insert2 (q := 3) (m := m) (n := n + 1) z a b y)
                    have hSi_split : Si = Si_cast + Si_last := by
                      -- Split the inner `i`-sum into `castSucc` and `last`, then distribute.
                      simp [Si, Si_cast, Si_last, z, Fin.sum_univ_castSucc, Finset.sum_add_distrib,
                        add_comm]

                    -- Split `Sj` into `j = 0` and `j > 0`.
                    let Sj_zero : Nat :=
                      ∑ b ∈ allowB, ∑ a ∈ allowA b,
                        B (insert2 (q := 3) (m := m + 1) (n := n) x a b y0)
                    let Sj_succ : Nat :=
                      ∑ b ∈ allowB, ∑ a ∈ allowA b, ∑ j : Fin n,
                        B (insert2 (q := 3) (m := m + 1) (n := n) x a b (erase (n := n) y j.succ))
                    have hSj_split : Sj = Sj_zero + Sj_succ := by
                      -- Split the inner `j`-sum into `0` and `succ`, then distribute.
                      -- We avoid `simp` here (it can be slow on the nested sums).
                      classical
                      dsimp [Sj, Sj_zero, Sj_succ, y0]
                      -- Rewrite the innermost `Fin (n+1)` sum pointwise.
                      have hinner :
                          ∀ b ∈ allowB, ∀ a ∈ allowA b,
                            (∑ j : Fin (n + 1),
                                  B (insert2 (q := 3) (m := m + 1) (n := n) x a b (erase (n := n) y j)))
                              =
                                B (insert2 (q := 3) (m := m + 1) (n := n) x a b (erase (n := n) y 0)) +
                                  ∑ j : Fin n,
                                    B (insert2 (q := 3) (m := m + 1) (n := n) x a b (erase (n := n) y j.succ)) := by
                        intro b hb a ha
                        simpa using
                          (Fin.sum_univ_succ
                            (f := fun j : Fin (n + 1) =>
                              B (insert2 (q := 3) (m := m + 1) (n := n) x a b (erase (n := n) y j))))
                      -- Apply the pointwise rewrite, then distribute the outer sums over `+`.
                      calc
                        (∑ b ∈ allowB, ∑ a ∈ allowA b, ∑ j : Fin (n + 1),
                            B (insert2 (q := 3) (m := m + 1) (n := n) x a b (erase (n := n) y j)))
                            =
                            ∑ b ∈ allowB, ∑ a ∈ allowA b,
                              (B (insert2 (q := 3) (m := m + 1) (n := n) x a b (erase (n := n) y 0)) +
                                ∑ j : Fin n,
                                  B (insert2 (q := 3) (m := m + 1) (n := n) x a b (erase (n := n) y j.succ))) := by
                              refine Finset.sum_congr rfl ?_
                              intro b hb
                              refine Finset.sum_congr rfl ?_
                              intro a ha
                              simpa using hinner b hb a ha
                          _ =
                              (∑ b ∈ allowB, ∑ a ∈ allowA b,
                                  B (insert2 (q := 3) (m := m + 1) (n := n) x a b (erase (n := n) y 0)))
                                +
                              (∑ b ∈ allowB, ∑ a ∈ allowA b, ∑ j : Fin n,
                                B (insert2 (q := 3) (m := m + 1) (n := n) x a b (erase (n := n) y j.succ))) := by
                                simp [Finset.sum_add_distrib]

                    -- Evaluate `Si_cast` using the induction hypothesis.
                    have hSi_cast :
                        Si_cast = c1 * (∑ i : Fin m, B (erase (n := m) x i.castSucc)) * B y := by
                      classical
                      -- Move the `i`-sum outward.
                      have hswap_ai :
                          (∑ b ∈ allowB, ∑ a ∈ allowA b, ∑ i : Fin m,
                              B (insert2 (q := 3) (m := m) (n := n + 1) (erase (n := m) x i.castSucc) a b y))
                            = ∑ b ∈ allowB, ∑ i : Fin m, ∑ a ∈ allowA b,
                                B (insert2 (q := 3) (m := m) (n := n + 1) (erase (n := m) x i.castSucc) a b y) := by
                        refine Finset.sum_congr rfl ?_
                        intro b hb
                        simpa using
                          (Finset.sum_comm (s := allowA b) (t := (Finset.univ : Finset (Fin m)))
                            (f := fun a i =>
                              B (insert2 (q := 3) (m := m) (n := n + 1) (erase (n := m) x i.castSucc) a b y)))
                      have hswap_bi :
                          (∑ b ∈ allowB, ∑ i : Fin m, ∑ a ∈ allowA b,
                              B (insert2 (q := 3) (m := m) (n := n + 1) (erase (n := m) x i.castSucc) a b y))
                            = ∑ i : Fin m, ∑ b ∈ allowB, ∑ a ∈ allowA b,
                                B (insert2 (q := 3) (m := m) (n := n + 1) (erase (n := m) x i.castSucc) a b y) := by
                        simpa using
                          (Finset.sum_comm (s := allowB) (t := (Finset.univ : Finset (Fin m)))
                            (f := fun b i =>
                              ∑ a ∈ allowA b,
                                B (insert2 (q := 3) (m := m) (n := n + 1) (erase (n := m) x i.castSucc) a b y)))
                      have hSi_cast' :
                          Si_cast
                            = ∑ i : Fin m, ∑ b ∈ allowB, ∑ a ∈ allowA b,
                                B (insert2 (q := 3) (m := m) (n := n + 1) (erase (n := m) x i.castSucc) a b y) := by
                        calc
                          Si_cast
                              = ∑ b ∈ allowB, ∑ a ∈ allowA b, ∑ i : Fin m,
                                  B (insert2 (q := 3) (m := m) (n := n + 1) (erase (n := m) x i.castSucc) a b y) := by
                                  rfl
                          _ = ∑ b ∈ allowB, ∑ i : Fin m, ∑ a ∈ allowA b,
                                  B (insert2 (q := 3) (m := m) (n := n + 1) (erase (n := m) x i.castSucc) a b y) := hswap_ai
                          _ = _ := hswap_bi

                      -- Now apply `ih` for each fixed `i`.
                      have hterm (i : Fin m) :
                          (∑ b ∈ allowB, ∑ a ∈ allowA b,
                                B (insert2 (q := 3) (m := m) (n := n + 1) (erase (n := m) x i.castSucc) a b y))
                            = c1 * B (erase (n := m) x i.castSucc) * B y := by
                        -- In the `i < last` case, `erase x i.castSucc` keeps the last letter `xm`.
                        -- So the restricted sum matches the unrestricted sum.
                        cases m with
                        | zero =>
                            exact i.elim0
                        | succ m =>
                            -- Rename the erased word.
                            let xi : Word 3 (m + 1) := erase (n := m + 1) x i.castSucc
                            have hlast : xi (Fin.last m) = xm := by
                              -- deleting a non-last position preserves the last letter
                              simp [xi, xm]

                            have hswap' :
                                (∑ a : Fin 3, ∑ b : Fin 3,
                                    B (insert2 (q := 3) (m := m + 1) (n := n + 1) xi a b y))
                                  = ∑ b : Fin 3, ∑ a : Fin 3,
                                      B (insert2 (q := 3) (m := m + 1) (n := n + 1) xi a b y) := by
                              simpa using
                                (Finset.sum_comm (s := (Finset.univ : Finset (Fin 3)))
                                  (t := (Finset.univ : Finset (Fin 3)))
                                  (f := fun a b =>
                                    B (insert2 (q := 3) (m := m + 1) (n := n + 1) xi a b y)))

                            have h_outer' :
                                (∑ b : Fin 3, ∑ a : Fin 3,
                                      B (insert2 (q := 3) (m := m + 1) (n := n + 1) xi a b y))
                                  = ∑ b ∈ allowB, ∑ a : Fin 3,
                                      B (insert2 (q := 3) (m := m + 1) (n := n + 1) xi a b y) := by
                              have h0 :
                                  (∑ a : Fin 3, B (insert2 (q := 3) (m := m + 1) (n := n + 1) xi a y1 y)) = 0 := by
                                have : ∀ a : Fin 3,
                                    B (insert2 (q := 3) (m := m + 1) (n := n + 1) xi a y1 y) = 0 := by
                                  intro a
                                  simpa [y1] using
                                    (B_insert2_eq_zero_of_eq_first (m := m) (n := n) (x := xi) (a := a) (y := y))
                                simp [this]
                              simpa [allowB, y1] using
                                (sum_univ_eq_sum_erase (a := y1)
                                  (f := fun b : Fin 3 =>
                                    ∑ a : Fin 3, B (insert2 (q := 3) (m := m + 1) (n := n + 1) xi a b y))
                                  (by simp [h0]))

                            have h_inner' (b : Fin 3) (hb : b ∈ allowB) :
                                (∑ a : Fin 3, B (insert2 (q := 3) (m := m + 1) (n := n + 1) xi a b y))
                                  = ∑ a ∈ allowA b,
                                      B (insert2 (q := 3) (m := m + 1) (n := n + 1) xi a b y) := by
                              have h0a :
                                  B (insert2 (q := 3) (m := m + 1) (n := n + 1) xi xm b y) = 0 := by
                                -- Here `xm` is the last letter of `xi`.
                                have : B (insert2 (q := 3) (m := m + 1) (n := n + 1) xi (xi (Fin.last m)) b y) = 0 := by
                                  simpa using
                                    (B_insert2_eq_zero_of_eq_last (m := m) (n := n) (x := xi) (b := b) (y := y))
                                simpa [hlast] using this
                              have h0b :
                                  B (insert2 (q := 3) (m := m + 1) (n := n + 1) xi b b y) = 0 := by
                                simpa using
                                  (B_insert2_eq_zero_of_eq_mid (m := m) (n := n) (x := xi) (a := b) (y := y))
                              simpa [allowA, xm] using
                                (sum_univ_eq_sum_erase_two (a := xm) (b := b)
                                  (f := fun a : Fin 3 =>
                                    B (insert2 (q := 3) (m := m + 1) (n := n + 1) xi a b y))
                                  (by simp [h0a]) (by simp [h0b]))

                            have h_restrict' :
                                (∑ a : Fin 3, ∑ b : Fin 3,
                                      B (insert2 (q := 3) (m := m + 1) (n := n + 1) xi a b y))
                                  = ∑ b ∈ allowB, ∑ a ∈ allowA b,
                                      B (insert2 (q := 3) (m := m + 1) (n := n + 1) xi a b y) := by
                              calc
                                (∑ a : Fin 3, ∑ b : Fin 3,
                                      B (insert2 (q := 3) (m := m + 1) (n := n + 1) xi a b y))
                                    = ∑ b : Fin 3, ∑ a : Fin 3,
                                        B (insert2 (q := 3) (m := m + 1) (n := n + 1) xi a b y) := hswap'
                                _ = ∑ b ∈ allowB, ∑ a : Fin 3,
                                        B (insert2 (q := 3) (m := m + 1) (n := n + 1) xi a b y) := h_outer'
                                _ = ∑ b ∈ allowB, ∑ a ∈ allowA b,
                                        B (insert2 (q := 3) (m := m + 1) (n := n + 1) xi a b y) := by
                                      refine Finset.sum_congr rfl ?_
                                      intro b hb
                                      simpa using h_inner' b hb

                            have hi_apply :
                                (∑ a : Fin 3, ∑ b : Fin 3,
                                      B (insert2 (q := 3) (m := m + 1) (n := n + 1) xi a b y))
                                  = c1 * B xi * B y := by
                              -- Apply `ih` with `hkx : m+1 + (n+1) = k`.
                              have hkx' : (m + 1) + (n + 1) = k := by
                                simpa using hkx
                              have hi := ih (x := xi) (y := y) hkx'
                              -- Identify the coefficient appearing in `hi` with `c1`.
                              have hcoef :
                                  2 * choose ((m + 1) + (n + 1) + 4) ((m + 1) + 2) = c1 := by
                                simp [c1, Nat.add_assoc, Nat.add_left_comm, Nat.add_comm]
                              -- Rewrite `hi` using `hcoef`.
                              simpa [hcoef, Nat.mul_assoc, Nat.mul_left_comm, Nat.mul_comm] using hi

                            -- Put the pieces together.
                            -- Start from the restricted sum and replace it by the unrestricted sum.
                            calc
                              (∑ b ∈ allowB, ∑ a ∈ allowA b,
                                    B (insert2 (q := 3) (m := m + 1) (n := n + 1) xi a b y))
                                  = ∑ a : Fin 3, ∑ b : Fin 3,
                                      B (insert2 (q := 3) (m := m + 1) (n := n + 1) xi a b y) := by
                                        simpa using h_restrict'.symm
                              _ = c1 * B xi * B y := hi_apply
                              _ = c1 * B (erase (n := m + 1) x i.castSucc) * B y := by
                                    rfl

                      -- Sum the `hterm` identities over `i`.
                      calc
                        Si_cast
                            = ∑ i : Fin m, ∑ b ∈ allowB, ∑ a ∈ allowA b,
                                B (insert2 (q := 3) (m := m) (n := n + 1) (erase (n := m) x i.castSucc) a b y) := hSi_cast'
                        _ = ∑ i : Fin m, (c1 * B (erase (n := m) x i.castSucc) * B y) := by
                              refine Finset.sum_congr rfl ?_
                              intro i hi
                              simpa using hterm i
                        _ = c1 * (∑ i : Fin m, B (erase (n := m) x i.castSucc)) * B y := by
                              -- Pull `B y` out of the `i`-sum, then pull `c1` out.
                              have hBy :
                                  (∑ i : Fin m, c1 * B (erase (n := m) x i.castSucc) * B y)
                                    = (∑ i : Fin m, c1 * B (erase (n := m) x i.castSucc)) * B y := by
                                -- Rewrite the summand to match `Finset.sum_mul`.
                                have hrewrite :
                                    (∑ i : Fin m, c1 * B (erase (n := m) x i.castSucc) * B y)
                                      = ∑ i : Fin m, (c1 * B (erase (n := m) x i.castSucc)) * B y := by
                                  refine Finset.sum_congr rfl ?_
                                  intro i hi
                                  simp [Nat.mul_assoc]
                                -- Now `sum_mul` applies.
                                simpa [hrewrite] using
                                  (Finset.sum_mul (s := (Finset.univ : Finset (Fin m)))
                                    (f := fun i : Fin m => c1 * B (erase (n := m) x i.castSucc)) (a := B y)).symm
                              have hc1 :
                                  (∑ i : Fin m, c1 * B (erase (n := m) x i.castSucc))
                                    = c1 * (∑ i : Fin m, B (erase (n := m) x i.castSucc)) := by
                                simpa using
                                  (Finset.mul_sum (s := (Finset.univ : Finset (Fin m)))
                                    (f := fun i : Fin m => B (erase (n := m) x i.castSucc)) (a := c1)).symm
                              -- Combine.
                              -- Rewrite the previous line using `hBy` and `hc1`.
                              calc
                                (∑ i : Fin m, c1 * B (erase (n := m) x i.castSucc) * B y)
                                    = (∑ i : Fin m, c1 * B (erase (n := m) x i.castSucc)) * B y := hBy
                                _ = (c1 * (∑ i : Fin m, B (erase (n := m) x i.castSucc))) * B y := by
                                      simp [hc1, Nat.mul_assoc]
                                _ = c1 * (∑ i : Fin m, B (erase (n := m) x i.castSucc)) * B y := by
                                      simp [Nat.mul_assoc]

                    -- Evaluate `Si_last + Sb` using the induction hypothesis on `z`.
                    have hSi_last_Sb :
                        Si_last + ∑ b ∈ allowB, B (insert1 (q := 3) (m := m + 1) (n := n + 1) x b y)
                          = c1 * B z * B y := by
                      classical
                      -- Rewrite `B (insert1 x b y)` as `B (insert2 z xm b y)`.
                      have hSb_as_insert2 :
                          (∑ b ∈ allowB, B (insert1 (q := 3) (m := m + 1) (n := n + 1) x b y))
                            = ∑ b ∈ allowB,
                                B (insert2 (q := 3) (m := m) (n := n + 1) z xm b y) := by
                          refine Finset.sum_congr rfl ?_
                          intro b hb
                          -- `insert2 z xm b y = insert1 x b y`
                          simpa [z] using
                            congrArg (B (q := 3))
                              (insert2_erase_last_eq_insert1 (m := m) (n := n) (x := x) (b := b) (y := y)).symm

                      -- For each `b`, adding the `a = xm` term completes the `a`-sum to the full sum over `Fin 3`.
                      let f : Fin 3 → Fin 3 → Nat :=
                        fun a b => B (insert2 (q := 3) (m := m) (n := n + 1) z a b y)
                      have hb_mid (b : Fin 3) : f b b = 0 := by
                        -- Not proper since the two inserted letters are equal.
                        have hsnoc : ¬ IsProper (snoc (snoc z b) b) := by
                          -- apply `not_isProper_snoc_self` to `snoc z b`
                          have : ¬ IsProper (snoc (snoc z b) ((snoc z b) (Fin.last m))) :=
                            Word.not_isProper_snoc_self (q := 3) (x := snoc z b)
                          simpa [Word.snoc] using this
                        have hnot : ¬ IsProper (insert2 (q := 3) (m := m) (n := n + 1) z b b y) := by
                          have : ¬ IsProper (append (snoc (snoc z b) b) y) :=
                            Word.not_isProper_append_left_of_not_isProper (q := 3)
                              (x := snoc (snoc z b) b) (y := y) hsnoc
                          simpa [Word.insert2, Word.append] using this
                        -- `insert2 z _ _ y` has length `m + 2 + (n + 1) = (m + 2 + n) + 1`.
                        simpa [f, Word.insert2, Nat.add_assoc, Nat.one_add] using
                          (B_eq_zero_of_not_isProper (q := 3)
                            (x := insert2 (q := 3) (m := m) (n := n + 1) z b b y)
                            (n := m + 2 + n) hnot)

                      have hb_first (a : Fin 3) : f a y1 = 0 := by
                        -- Boundary failure between `y1` and `y 0`.
                        have hbd : (snoc (snoc z a) y1) (Fin.last (m + 1)) = y 0 := by
                          simp [y1, Word.snoc]
                        have hnot : ¬ IsProper (insert2 (q := 3) (m := m) (n := n + 1) z a y1 y) := by
                          have : ¬ IsProper (append (snoc (snoc z a) y1) y) :=
                            Word.not_isProper_append_of_eq_boundary (q := 3)
                              (x := snoc (snoc z a) y1) (y := y) (by simpa using hbd)
                          simpa [Word.insert2, Word.append] using this
                        simpa [f, Word.insert2, Nat.add_assoc, Nat.one_add] using
                          (B_eq_zero_of_not_isProper (q := 3)
                            (x := insert2 (q := 3) (m := m) (n := n + 1) z a y1 y)
                            (n := m + 2 + n) hnot)

                      have h_complete (b : Fin 3) (hb : b ∈ allowB) :
                          (∑ a ∈ allowA b, f a b) + f xm b = ∑ a : Fin 3, f a b := by
                        -- First remove the `a = b` term (it is zero).
                        have hsum_all :
                            (∑ a : Fin 3, f a b) = ∑ a ∈ (Finset.univ.erase b), f a b := by
                          simpa using sum_univ_eq_sum_erase (a := b) (f := fun a => f a b) (hb_mid b)
                        -- Now split out the `a = xm` term from `univ.erase b`.
                        by_cases hbx : xm = b
                        · subst hbx
                          -- Here `allowA b = univ.erase b` and `f xm b = f b b = 0`.
                          simpa [allowA, f, hb_mid xm, Finset.erase_idem, add_comm] using hsum_all.symm
                        · have hxm_mem : xm ∈ (Finset.univ.erase b) := by
                            simp [Finset.mem_erase, hbx]
                          have hsplit_xm :
                              (∑ a ∈ (Finset.univ.erase b), f a b)
                                = (∑ a ∈ ((Finset.univ.erase b).erase xm), f a b) + f xm b := by
                            simpa using
                              (Finset.sum_erase_add (s := (Finset.univ.erase b)) (a := xm)
                                (f := fun a => f a b) hxm_mem).symm
                          -- Rewrite `((univ.erase b).erase xm)` to `allowA b`.
                          have herase_comm :
                              ((Finset.univ.erase b).erase xm) = (Finset.univ.erase xm).erase b := by
                            classical
                            ext a
                            simp [Finset.mem_erase, and_comm]
                          -- Finish.
                          calc
                            (∑ a ∈ allowA b, f a b) + f xm b
                                = (∑ a ∈ ((Finset.univ.erase b).erase xm), f a b) + f xm b := by
                                    simp [allowA, herase_comm]
                            _ = ∑ a ∈ (Finset.univ.erase b), f a b := by
                                  exact hsplit_xm.symm
                            _ = ∑ a : Fin 3, f a b := by
                                  exact hsum_all.symm

                      -- Combine the completed `a`-sum over `b ∈ allowB` and add back the missing `b = y1` term (it is zero).
                      have hsum_z :
                          Si_last + ∑ b ∈ allowB, f xm b = ∑ a : Fin 3, ∑ b : Fin 3, f a b := by
                        -- Expand `Si_last` and use `h_complete` to replace each inner sum.
                        have :
                            Si_last + ∑ b ∈ allowB, f xm b
                              = ∑ b ∈ allowB, (∑ a : Fin 3, f a b) := by
                            -- group by `b`
                            calc
                              Si_last + ∑ b ∈ allowB, f xm b
                                  = (∑ b ∈ allowB, (∑ a ∈ allowA b, f a b)) + ∑ b ∈ allowB, f xm b := by
                                        rfl
                              _ = ∑ b ∈ allowB, ((∑ a ∈ allowA b, f a b) + f xm b) := by
                                    simp [Finset.sum_add_distrib]
                              _ = ∑ b ∈ allowB, (∑ a : Fin 3, f a b) := by
                                    refine Finset.sum_congr rfl ?_
                                    intro b hb
                                    simpa using h_complete b hb
                        -- Now swap the `a` and `b` sums to match `∑ a, ∑ b`.
                        calc
                          Si_last + ∑ b ∈ allowB, f xm b
                              = ∑ b ∈ allowB, (∑ a : Fin 3, f a b) := this
                          _ = ∑ b : Fin 3, ∑ a : Fin 3, f a b := by
                                -- add the missing `b = y1` term (it is zero)
                                have h0b : (∑ a : Fin 3, f a y1) = 0 := by
                                  have : ∀ a : Fin 3, f a y1 = 0 := by
                                    intro a
                                    simpa [f] using hb_first a
                                  simp [this]
                                simpa [allowB] using
                                  (sum_univ_eq_sum_erase (a := y1) (f := fun b => ∑ a : Fin 3, f a b) h0b).symm
                          _ = ∑ a : Fin 3, ∑ b : Fin 3, f a b := by
                                simpa using
                                  (Finset.sum_comm (s := (Finset.univ : Finset (Fin 3)))
                                    (t := (Finset.univ : Finset (Fin 3)))
                                    (f := fun b a => f a b))

                      -- Apply `ih` to the unrestricted sum for `(z, y)`.
                      have hiz :
                          (∑ a : Fin 3, ∑ b : Fin 3, f a b) = c1 * B z * B y := by
                        -- `ih` gives the coefficient with `m + (n+1) = k`.
                        have hkx' : m + (n + 1) = k := hkx
                        -- Rewrite `c1` and use `ih`.
                        simpa [c1, f, Nat.add_assoc, Nat.one_add] using
                          (ih (x := z) (y := y) hkx')

                      -- Finish.
                      calc
                        Si_last + ∑ b ∈ allowB, B (insert1 (q := 3) (m := m + 1) (n := n + 1) x b y)
                            = Si_last + ∑ b ∈ allowB, f xm b := by
                                  simp [hSb_as_insert2, f]
                        _ = ∑ a : Fin 3, ∑ b : Fin 3, f a b := hsum_z
                        _ = c1 * B z * B y := hiz

                    -- Evaluate `Sj_succ` using the induction hypothesis (for deletions in `y` away from index `0`).
                    have hSj_succ :
                        Sj_succ = c2 * B x * (∑ j : Fin n, B (erase (n := n) y j.succ)) := by
                      classical
                      -- Move the `j`-sum outward.
                      have hswap_aj :
                          (∑ b ∈ allowB, ∑ a ∈ allowA b, ∑ j : Fin n,
                              B (insert2 (q := 3) (m := m + 1) (n := n) x a b (erase (n := n) y j.succ)))
                            = ∑ b ∈ allowB, ∑ j : Fin n, ∑ a ∈ allowA b,
                                B (insert2 (q := 3) (m := m + 1) (n := n) x a b (erase (n := n) y j.succ)) := by
                        refine Finset.sum_congr rfl ?_
                        intro b hb
                        simpa using
                          (Finset.sum_comm (s := allowA b) (t := (Finset.univ : Finset (Fin n)))
                            (f := fun a j =>
                              B (insert2 (q := 3) (m := m + 1) (n := n) x a b (erase (n := n) y j.succ))))
                      have hswap_bj :
                          (∑ b ∈ allowB, ∑ j : Fin n, ∑ a ∈ allowA b,
                              B (insert2 (q := 3) (m := m + 1) (n := n) x a b (erase (n := n) y j.succ)))
                            = ∑ j : Fin n, ∑ b ∈ allowB, ∑ a ∈ allowA b,
                                B (insert2 (q := 3) (m := m + 1) (n := n) x a b (erase (n := n) y j.succ)) := by
                        simpa using
                          (Finset.sum_comm (s := allowB) (t := (Finset.univ : Finset (Fin n)))
                            (f := fun b j =>
                              ∑ a ∈ allowA b,
                                B (insert2 (q := 3) (m := m + 1) (n := n) x a b (erase (n := n) y j.succ))))
                      have hSj_succ' :
                          Sj_succ
                            = ∑ j : Fin n, ∑ b ∈ allowB, ∑ a ∈ allowA b,
                                B (insert2 (q := 3) (m := m + 1) (n := n) x a b (erase (n := n) y j.succ)) := by
                        calc
                          Sj_succ
                              = ∑ b ∈ allowB, ∑ a ∈ allowA b, ∑ j : Fin n,
                                  B (insert2 (q := 3) (m := m + 1) (n := n) x a b (erase (n := n) y j.succ)) := by
                                  rfl
                          _ = ∑ b ∈ allowB, ∑ j : Fin n, ∑ a ∈ allowA b,
                                  B (insert2 (q := 3) (m := m + 1) (n := n) x a b (erase (n := n) y j.succ)) := hswap_aj
                          _ = _ := hswap_bj

                      have hterm (j : Fin n) :
                          (∑ b ∈ allowB, ∑ a ∈ allowA b,
                                B (insert2 (q := 3) (m := m + 1) (n := n) x a b (erase (n := n) y j.succ)))
                            = c2 * B x * B (erase (n := n) y j.succ) := by
                        -- For `j.succ`, `erase y j.succ` keeps the first letter `y1`.
                        cases n with
                        | zero =>
                            exact j.elim0
                        | succ n =>
                            let yj : Word 3 (n + 1) := erase (n := n + 1) y j.succ
                            have hfirst : yj 0 = y1 := by
                              simp [yj, y1]

                            -- As before, the restricted sum matches the unrestricted sum for `(x, yj)`.
                            have hswap' :
                                (∑ a : Fin 3, ∑ b : Fin 3,
                                    B (insert2 (q := 3) (m := m + 1) (n := n + 1) x a b yj))
                                  = ∑ b : Fin 3, ∑ a : Fin 3,
                                      B (insert2 (q := 3) (m := m + 1) (n := n + 1) x a b yj) := by
                              simpa using
                                (Finset.sum_comm (s := (Finset.univ : Finset (Fin 3)))
                                  (t := (Finset.univ : Finset (Fin 3)))
                                  (f := fun a b =>
                                    B (insert2 (q := 3) (m := m + 1) (n := n + 1) x a b yj)))

                            have h_outer' :
                                (∑ b : Fin 3, ∑ a : Fin 3,
                                      B (insert2 (q := 3) (m := m + 1) (n := n + 1) x a b yj))
                                  = ∑ b ∈ allowB, ∑ a : Fin 3,
                                      B (insert2 (q := 3) (m := m + 1) (n := n + 1) x a b yj) := by
                              have h0 :
                                  (∑ a : Fin 3, B (insert2 (q := 3) (m := m + 1) (n := n + 1) x a y1 yj)) = 0 := by
                                have : ∀ a : Fin 3,
                                    B (insert2 (q := 3) (m := m + 1) (n := n + 1) x a y1 yj) = 0 := by
                                  intro a
                                  -- boundary failure: `y1 = yj 0`
                                  have : B (insert2 (q := 3) (m := m + 1) (n := n + 1) x a (yj 0) yj) = 0 := by
                                    simpa using
                                      (B_insert2_eq_zero_of_eq_first (m := m) (n := n) (x := x) (a := a) (y := yj))
                                  simpa [hfirst] using this
                                simp [this]
                              simpa [allowB, y1] using
                                (sum_univ_eq_sum_erase (a := y1)
                                  (f := fun b : Fin 3 =>
                                    ∑ a : Fin 3, B (insert2 (q := 3) (m := m + 1) (n := n + 1) x a b yj))
                                  (by simp [h0]))

                            have h_inner' (b : Fin 3) (hb : b ∈ allowB) :
                                (∑ a : Fin 3, B (insert2 (q := 3) (m := m + 1) (n := n + 1) x a b yj))
                                  = ∑ a ∈ allowA b,
                                      B (insert2 (q := 3) (m := m + 1) (n := n + 1) x a b yj) := by
                              have h0a :
                                  B (insert2 (q := 3) (m := m + 1) (n := n + 1) x xm b yj) = 0 := by
                                simpa [xm] using
                                  (B_insert2_eq_zero_of_eq_last (m := m) (n := n) (x := x) (b := b) (y := yj))
                              have h0b :
                                  B (insert2 (q := 3) (m := m + 1) (n := n + 1) x b b yj) = 0 := by
                                simpa using
                                  (B_insert2_eq_zero_of_eq_mid (m := m) (n := n) (x := x) (a := b) (y := yj))
                              simpa [allowA, xm] using
                                (sum_univ_eq_sum_erase_two (a := xm) (b := b)
                                  (f := fun a : Fin 3 =>
                                    B (insert2 (q := 3) (m := m + 1) (n := n + 1) x a b yj))
                                  (by simp [h0a]) (by simp [h0b]))

                            have h_restrict' :
                                (∑ a : Fin 3, ∑ b : Fin 3,
                                      B (insert2 (q := 3) (m := m + 1) (n := n + 1) x a b yj))
                                  = ∑ b ∈ allowB, ∑ a ∈ allowA b,
                                      B (insert2 (q := 3) (m := m + 1) (n := n + 1) x a b yj) := by
                              calc
                                (∑ a : Fin 3, ∑ b : Fin 3,
                                      B (insert2 (q := 3) (m := m + 1) (n := n + 1) x a b yj))
                                    = ∑ b : Fin 3, ∑ a : Fin 3,
                                        B (insert2 (q := 3) (m := m + 1) (n := n + 1) x a b yj) := hswap'
                                _ = ∑ b ∈ allowB, ∑ a : Fin 3,
                                        B (insert2 (q := 3) (m := m + 1) (n := n + 1) x a b yj) := h_outer'
                                _ = ∑ b ∈ allowB, ∑ a ∈ allowA b,
                                        B (insert2 (q := 3) (m := m + 1) (n := n + 1) x a b yj) := by
                                      refine Finset.sum_congr rfl ?_
                                      intro b hb
                                      simpa using h_inner' b hb

                            have hi_apply :
                                (∑ a : Fin 3, ∑ b : Fin 3,
                                      B (insert2 (q := 3) (m := m + 1) (n := n + 1) x a b yj))
                                  = c2 * B x * B yj := by
                              have hky' : (m + 1) + (n + 1) = k := by
                                simpa using hky
                              have hi := ih (x := x) (y := yj) hky'
                              have hcoef :
                                  2 * choose ((m + 1) + (n + 1) + 4) ((m + 1) + 2) = c2 := by
                                simp [c2, Nat.add_assoc, Nat.add_left_comm, Nat.add_comm]
                              simpa [hcoef, Nat.mul_assoc, Nat.mul_left_comm, Nat.mul_comm] using hi

                            calc
                              (∑ b ∈ allowB, ∑ a ∈ allowA b,
                                    B (insert2 (q := 3) (m := m + 1) (n := n + 1) x a b yj))
                                  = ∑ a : Fin 3, ∑ b : Fin 3,
                                      B (insert2 (q := 3) (m := m + 1) (n := n + 1) x a b yj) := by
                                        simpa using h_restrict'.symm
                              _ = c2 * B x * B yj := hi_apply
                              _ = c2 * B x * B (erase (n := n + 1) y j.succ) := by rfl

                      -- Sum the `hterm` identities over `j`.
                      calc
                        Sj_succ
                            = ∑ j : Fin n, ∑ b ∈ allowB, ∑ a ∈ allowA b,
                                B (insert2 (q := 3) (m := m + 1) (n := n) x a b (erase (n := n) y j.succ)) := hSj_succ'
                        _ = ∑ j : Fin n, (c2 * B x * B (erase (n := n) y j.succ)) := by
                                refine Finset.sum_congr rfl ?_
                                intro j hj
                                simpa using hterm j
                        _ = c2 * B x * (∑ j : Fin n, B (erase (n := n) y j.succ)) := by
                                -- factor out `c2 * B x`
                                simp [Finset.mul_sum, Nat.mul_assoc]

                    -- Evaluate `Sj_zero + Sa` using the induction hypothesis on `y0`.
                    have hSj_zero_Sa :
                        Sj_zero + ∑ a ∈ (Finset.univ.erase xm),
                            B (insert1 (q := 3) (m := m + 1) (n := n + 1) x a y)
                          = c2 * B x * B y0 := by
                      classical
                      -- Rewrite the `Sa` term using `B_insert1_eq_B_insert2_erase_zero`.
                      have hSa_as_insert2 :
                          (∑ a ∈ (Finset.univ.erase xm),
                              B (insert1 (q := 3) (m := m + 1) (n := n + 1) x a y))
                            = ∑ a ∈ (Finset.univ.erase xm),
                                B (insert2 (q := 3) (m := m + 1) (n := n) x a y1 y0) := by
                          refine Finset.sum_congr rfl ?_
                          intro a ha
                          simpa [y0] using
                            (B_insert1_eq_B_insert2_erase_zero (m := m) (n := n) (x := x) (a := a) (y := y))

                      -- Swap the dependent sums in `Sj_zero` to sum over `a` first.
                      have hswapSj0 :
                          Sj_zero
                            = ∑ a ∈ (Finset.univ.erase xm), ∑ b ∈ (Finset.univ.erase y1).erase a,
                                B (insert2 (q := 3) (m := m + 1) (n := n) x a b y0) := by
                        -- same membership equivalence as in `hSa`
                        have hmem :
                            ∀ b a : Fin 3,
                              b ∈ allowB ∧ a ∈ allowA b ↔ b ∈ ((Finset.univ.erase y1).erase a) ∧ a ∈ (Finset.univ.erase xm) := by
                          intro b a
                          constructor
                          · rintro ⟨hb, ha⟩
                            have hb_ne_y1 : b ≠ y1 := (Finset.mem_erase.mp hb).1
                            have ha_ne_b : a ≠ b := (Finset.mem_erase.mp ha).1
                            have ha_mem_univ_erase_xm : a ∈ (Finset.univ.erase xm) := (Finset.mem_erase.mp ha).2
                            refine ⟨?_, ha_mem_univ_erase_xm⟩
                            refine Finset.mem_erase.mpr ?_
                            refine ⟨ha_ne_b.symm, ?_⟩
                            exact Finset.mem_erase.mpr ⟨hb_ne_y1, Finset.mem_univ b⟩
                          · rintro ⟨hb, ha⟩
                            have hb_ne_a : b ≠ a := (Finset.mem_erase.mp hb).1
                            have hb_mem_univ_erase_y1 : b ∈ (Finset.univ.erase y1) := (Finset.mem_erase.mp hb).2
                            have hb_ne_y1 : b ≠ y1 := (Finset.mem_erase.mp hb_mem_univ_erase_y1).1
                            refine ⟨?_, ?_⟩
                            · exact Finset.mem_erase.mpr ⟨hb_ne_y1, Finset.mem_univ b⟩
                            · exact Finset.mem_erase.mpr ⟨hb_ne_a.symm, ha⟩
                        simpa [Sj_zero] using
                          (Finset.sum_comm' (s := allowB) (t := allowA)
                            (t' := (Finset.univ.erase xm)) (s' := fun a => (Finset.univ.erase y1).erase a)
                            (f := fun b a => B (insert2 (q := 3) (m := m + 1) (n := n) x a b y0)) hmem)

                      -- Use the induction hypothesis for the unrestricted sum over `a,b : Fin 3`.
                      let g : Fin 3 → Fin 3 → Nat :=
                        fun a b => B (insert2 (q := 3) (m := m + 1) (n := n) x a b y0)

                      -- `g a a = 0` since the inserted letters are equal, so the word is not proper.
                      have hb_mid (a : Fin 3) : g a a = 0 := by
                        have hsnoc : ¬ IsProper (snoc (snoc x a) a) := by
                          simpa [Word.snoc] using (Word.not_isProper_snoc_self (q := 3) (x := snoc x a))
                        have hnot : ¬ IsProper (insert2 (q := 3) (m := m + 1) (n := n) x a a y0) := by
                          cases n with
                          | zero =>
                              -- `y0` is empty, so `insert2` is just the double `snoc`.
                              have hy0 : y0 = emptyWord := Subsingleton.elim _ _
                              -- `y0` is a local definition, so we rewrite rather than `subst`.
                              rw [hy0]
                              simpa [insert2_empty_right] using hsnoc
                          | succ n =>
                              have : ¬ IsProper (append (snoc (snoc x a) a) y0) :=
                                Word.not_isProper_append_left_of_not_isProper (q := 3)
                                  (x := snoc (snoc x a) a) (y := y0) hsnoc
                              simpa [Word.insert2, Word.append] using this
                        -- Align lengths using a cast, then apply `B_eq_zero_of_not_isProper`.
                        have hlen : (m + 1) + 2 + n = (m + n + 2) + 1 := by
                          ac_rfl
                        have hnot' :
                            ¬ IsProper (Word.cast (q := 3) hlen
                              (insert2 (q := 3) (m := m + 1) (n := n) x a a y0)) := by
                          simpa [Word.isProper_cast_iff] using hnot
                        have hB0 :
                            B (Word.cast (q := 3) hlen
                              (insert2 (q := 3) (m := m + 1) (n := n) x a a y0)) = 0 := by
                          simpa using
                            (B_eq_zero_of_not_isProper (q := 3)
                              (x := Word.cast (q := 3) hlen
                                (insert2 (q := 3) (m := m + 1) (n := n) x a a y0))
                              (n := m + n + 2) hnot')
                        simpa [g, B_cast] using hB0

                      -- `g xm b = 0` since `a = xm` repeats the last letter of `x`.
                      have hb_last (b : Fin 3) : g xm b = 0 := by
                        have hsnoc : ¬ IsProper (snoc x xm) := by
                          simpa [xm] using (Word.not_isProper_snoc_self (q := 3) (x := x))
                        have hsnoc2 : ¬ IsProper (snoc (snoc x xm) b) := by
                          intro h
                          exact hsnoc (isProper_of_isProper_snoc (x := snoc x xm) (a := b) h)
                        have hnot : ¬ IsProper (insert2 (q := 3) (m := m + 1) (n := n) x xm b y0) := by
                          cases n with
                          | zero =>
                              have hy0 : y0 = emptyWord := Subsingleton.elim _ _
                              rw [hy0]
                              simpa [insert2_empty_right] using hsnoc2
                          | succ n =>
                              have : ¬ IsProper (append (snoc (snoc x xm) b) y0) :=
                                Word.not_isProper_append_left_of_not_isProper (q := 3)
                                  (x := snoc (snoc x xm) b) (y := y0) hsnoc2
                              simpa [Word.insert2, Word.append] using this
                        have hlen : (m + 1) + 2 + n = (m + n + 2) + 1 := by
                          ac_rfl
                        have hnot' :
                            ¬ IsProper (Word.cast (q := 3) hlen
                              (insert2 (q := 3) (m := m + 1) (n := n) x xm b y0)) := by
                          simpa [Word.isProper_cast_iff] using hnot
                        have hB0 :
                            B (Word.cast (q := 3) hlen
                              (insert2 (q := 3) (m := m + 1) (n := n) x xm b y0)) = 0 := by
                          simpa using
                            (B_eq_zero_of_not_isProper (q := 3)
                              (x := Word.cast (q := 3) hlen
                                (insert2 (q := 3) (m := m + 1) (n := n) x xm b y0))
                              (n := m + n + 2) hnot')
                        simpa [g, B_cast] using hB0

                      -- For each `a`, the `(b ≠ y1, b ≠ a)` sum together with the `b = y1` term
                      -- matches the full sum over `b : Fin 3` (since `g a a = 0`).
                      have hsum_b (a : Fin 3) :
                          (∑ b : Fin 3, g a b)
                            = (∑ b ∈ (Finset.univ.erase y1).erase a, g a b) + g a y1 := by
                        classical
                        -- First remove the `b = a` term.
                        have h1 :
                            (∑ b : Fin 3, g a b) = ∑ b ∈ (Finset.univ.erase a), g a b :=
                          sum_univ_eq_sum_erase (a := a) (f := fun b => g a b) (hb_mid a)
                        by_cases hay : a = y1
                        · subst hay
                          -- `((univ.erase a).erase a) = (univ.erase a)` and `g a a = 0`.
                          have ha_not_mem : (y1 : Fin 3) ∉ (Finset.univ.erase y1) := by
                            simp
                          have herase : (Finset.univ.erase y1).erase y1 = (Finset.univ.erase y1) := by
                            exact Finset.erase_eq_of_notMem ha_not_mem
                          -- `g y1 y1 = 0` kills the extra term.
                          simp [h1, hb_mid y1]
                        · have hy1_mem : y1 ∈ (Finset.univ.erase a) := by
                            refine Finset.mem_erase.mpr ?_
                            refine ⟨?_, Finset.mem_univ y1⟩
                            intro h
                            exact hay h.symm
                          have h2 :=
                            (Finset.sum_erase_add (s := (Finset.univ.erase a)) (a := y1)
                              (f := fun b => g a b) hy1_mem).symm
                          have herase :
                              (Finset.univ.erase a).erase y1 = (Finset.univ.erase y1).erase a := by
                            ext b
                            simp [Finset.mem_erase, and_comm]
                          calc
                            (∑ b : Fin 3, g a b) = ∑ b ∈ (Finset.univ.erase a), g a b := h1
                            _ = (∑ b ∈ ((Finset.univ.erase a).erase y1), g a b) + g a y1 := by
                                  simpa using h2
                            _ = (∑ b ∈ (Finset.univ.erase y1).erase a, g a b) + g a y1 := by
                                  simp [herase]

                      -- Apply `ih` directly: the unrestricted sum equals the RHS for `(x, y0)`.
                      have hi_xy0 :
                          (∑ a : Fin 3, ∑ b : Fin 3, g a b) = c2 * B x * B y0 := by
                        have hky0 : (m + 1) + n = k := hky
                        simpa [c2, g, y0, Nat.add_assoc, Nat.one_add] using
                          (ih (x := x) (y := y0) hky0)

                      -- Now assemble `Sj_zero + Sa` into the unrestricted sum and apply `ih`.
                      have hxm0 : (∑ b : Fin 3, g xm b) = 0 := by
                        simp [hb_last]
                      have hsum_a :
                          (∑ a : Fin 3, ∑ b : Fin 3, g a b)
                            = ∑ a ∈ (Finset.univ.erase xm), ∑ b : Fin 3, g a b := by
                        -- Remove the `a = xm` term, which is zero.
                        simpa using
                          (sum_univ_eq_sum_erase (a := xm) (f := fun a => ∑ b : Fin 3, g a b) hxm0)
                      calc
                        Sj_zero + ∑ a ∈ (Finset.univ.erase xm),
                            B (insert1 (q := 3) (m := m + 1) (n := n + 1) x a y)
                            = Sj_zero + ∑ a ∈ (Finset.univ.erase xm),
                                g a y1 := by
                                  simp [hSa_as_insert2, g]
                        _ = (∑ a ∈ (Finset.univ.erase xm), ∑ b ∈ (Finset.univ.erase y1).erase a, g a b)
                              + (∑ a ∈ (Finset.univ.erase xm), g a y1) := by
                                  simp [hswapSj0, g]
                        _ = ∑ a ∈ (Finset.univ.erase xm),
                              ((∑ b ∈ (Finset.univ.erase y1).erase a, g a b) + g a y1) := by
                                  -- Combine the two outer sums.
                                  symm
                                  simp [Finset.sum_add_distrib]
                        _ = ∑ a ∈ (Finset.univ.erase xm), ∑ b : Fin 3, g a b := by
                                  refine Finset.sum_congr rfl ?_
                                  intro a ha
                                  simp [hsum_b a]
                        _ = ∑ a : Fin 3, ∑ b : Fin 3, g a b := by
                                  -- Extend the `a`-sum to all of `Fin 3` (the missing term is zero).
                                  simpa [Finset.sum_sigma'] using hsum_a.symm
                        _ = c2 * B x * B y0 := hi_xy0

                    -- Now assemble everything.
                    have hxB' : B x = (∑ i : Fin m, B (erase (n := m) x i.castSucc)) + B z := by
                      have hxSplit :
                          (∑ i : Fin (m + 1), B (erase (n := m) x i))
                            = (∑ i : Fin m, B (erase (n := m) x i.castSucc)) + B z := by
                          simpa [z] using
                            (Fin.sum_univ_castSucc (f := fun i : Fin (m + 1) => B (erase (n := m) x i)))
                      simpa [hxSplit] using hxB
                    have hyB' : B y = B y0 + (∑ j : Fin n, B (erase (n := n) y j.succ)) := by
                      have hySplit :
                          (∑ j : Fin (n + 1), B (erase (n := n) y j))
                            = B y0 + (∑ j : Fin n, B (erase (n := n) y j.succ)) := by
                          simpa [y0] using
                            (Fin.sum_univ_succ (f := fun j : Fin (n + 1) => B (erase (n := n) y j)))
                      simpa [hySplit] using hyB

                    have hx_side :
                        Si + Sb = c1 * B x * B y := by
                      -- Use `hSi_split` and `hSb`, and fold `hxB'`.
                      calc
                        Si + Sb = (Si_cast + Si_last) + (∑ b ∈ allowB, B (insert1 (q := 3) (m := m + 1) (n := n + 1) x b y)) := by
                                  simp [hSi_split, hSb, add_assoc]
                        _ = (c1 * (∑ i : Fin m, B (erase (n := m) x i.castSucc)) * B y)
                              + (c1 * B z * B y) := by
                                  simp [hSi_cast, hSi_last_Sb, add_assoc]
                        _ = c1 * ((∑ i : Fin m, B (erase (n := m) x i.castSucc)) + B z) * B y := by
                                  simp [Nat.mul_add, Nat.mul_left_comm, Nat.mul_comm]
                        _ = c1 * B x * B y := by
                                  simp [hxB']

                    have hy_side :
                        Sa + Sj = c2 * B x * B y := by
                      -- Use `hSj_split` and `hSa`, and fold `hyB'`.
                      classical
                      let A : ℕ :=
                        ∑ a ∈ (Finset.univ.erase xm), B (insert1 (q := 3) (m := m + 1) (n := n + 1) x a y)
                      calc
                        Sa + Sj = A + (Sj_zero + Sj_succ) := by
                                  simp [hSa, hSj_split, A]
                        _ = (Sj_zero + A) + Sj_succ := by
                                  -- Reassociate and commute to match `hSj_zero_Sa`.
                                  simp [A, add_assoc, add_comm]
                        _ = (c2 * B x * B y0) + Sj_succ := by
                                  simpa [A, add_assoc] using congrArg (fun t => t + Sj_succ) hSj_zero_Sa
                        _ =
                            (c2 * B x * B y0) + (c2 * B x * (∑ j : Fin n, B (erase (n := n) y j.succ))) := by
                              simp [hSj_succ]
                        _ = c2 * B x * (B y0 + (∑ j : Fin n, B (erase (n := n) y j.succ))) := by
                              simp [Nat.mul_add, Nat.mul_assoc]
                        _ = c2 * B x * B y := by
                              simp [hyB']

                    have hpascal :
                        choose (m + n + 6) (m + 3) = choose (m + n + 5) (m + 2) + choose (m + n + 5) (m + 3) := by
                      simpa using (Nat.choose_succ_succ (n := m + n + 5) (k := m + 2))

                    -- Finally close the goal.
                    have hgoal :
                        (∑ a : Fin 3, ∑ b : Fin 3, B (insert2 (q := 3) (m := m + 1) (n := n + 1) x a b y))
                          = 2 * choose (m + n + 6) (m + 3) * B x * B y := by
                      -- Start from the decomposition, then use `hx_side` and `hy_side`.
                      have htotal :
                          (∑ a : Fin 3, ∑ b : Fin 3, B (insert2 (q := 3) (m := m + 1) (n := n + 1) x a b y))
                            = Si + Sb + Sa + Sj := by
                              calc
                                (∑ a : Fin 3, ∑ b : Fin 3, B (insert2 (q := 3) (m := m + 1) (n := n + 1) x a b y))
                                    = ∑ b ∈ allowB, ∑ a ∈ allowA b,
                                        B (insert2 (q := 3) (m := m + 1) (n := n + 1) x a b y) := h_restrict
                                _ = ∑ b ∈ allowB, ∑ a ∈ allowA b,
                                      ((∑ i : Fin (m + 1),
                                            B (insert2 (q := 3) (m := m) (n := n + 1) (erase (n := m) x i) a b y))
                                        + B (insert1 (q := 3) (m := m + 1) (n := n + 1) x b y)
                                        + B (insert1 (q := 3) (m := m + 1) (n := n + 1) x a y)
                                        + ∑ j : Fin (n + 1),
                                            B (insert2 (q := 3) (m := m + 1) (n := n) x a b (erase (n := n) y j))) := h_main
                                _ = Si + Sb + Sa + Sj := by
                                      simpa [Si, Sb, Sa, Sj] using hsplit
                      -- Now group as `(Si + Sb) + (Sa + Sj)`.
                      calc
                        (∑ a : Fin 3, ∑ b : Fin 3, B (insert2 (q := 3) (m := m + 1) (n := n + 1) x a b y))
                            = (Si + Sb) + (Sa + Sj) := by
                                  simp [htotal, add_assoc, add_left_comm, add_comm]
                        _ = (c1 * B x * B y) + (c2 * B x * B y) := by
                                  simp [hx_side, hy_side]
                        _ = 2 * (choose (m + n + 5) (m + 2) + choose (m + n + 5) (m + 3)) * B x * B y := by
                                  simp [c1, c2, Nat.mul_add, Nat.add_mul, Nat.mul_assoc, add_assoc]
                        _ = 2 * choose (m + n + 6) (m + 3) * B x * B y := by
                                  -- Rewrite the inner sum using Pascal's identity.
                                  rw [hpascal.symm]

                    -- Rewrite the goal to match the theorem statement.
                    have h₁ : m + n + 6 = (m + 1) + (n + 1) + 4 := by
                      ac_rfl
                    have h₂ : m + 3 = (m + 1) + 2 := by
                      ac_rfl
                    refine hgoal.trans ?_
                    rw [h₁, h₂]
                  · -- `y` not proper: both sides are `0`.
                    have hy0 : B y = 0 := B_eq_zero_of_not_isProper (q := 3) (x := y) (n := n) hy
                    have hterm (a b : Fin 3) :
                        B (insert2 (q := 3) (m := m + 1) (n := n + 1) x a b y) = 0 := by
                      -- Not proper because the right block is not proper.
                      have : ¬ IsProper (insert2 (q := 3) (m := m + 1) (n := n + 1) x a b y) := by
                        have : ¬ IsProper y := hy
                        have : ¬ IsProper (append (snoc (snoc x a) b) y) :=
                          Word.not_isProper_append_right_of_not_isProper (q := 3)
                            (x := snoc (snoc x a) b) (y := y) this
                        simpa [Word.insert2, Word.append] using this
                      simpa [Word.insert2, Nat.add_assoc, Nat.one_add] using
                        (B_eq_zero_of_not_isProper (q := 3)
                          (x := insert2 (q := 3) (m := m + 1) (n := n + 1) x a b y)
                          (n := (m + 1) + 2 + n) this)
                    have hleft :
                        (∑ a : Fin 3, ∑ b : Fin 3, B (insert2 (q := 3) (m := m + 1) (n := n + 1) x a b y)) = 0 := by
                      simp [hterm]
                    simp [hleft, hy0]
                · -- `x` not proper: both sides are `0`.
                  have hx0 : B x = 0 := B_eq_zero_of_not_isProper (q := 3) (x := x) (n := m) hx
                  have hterm (a b : Fin 3) :
                      B (insert2 (q := 3) (m := m + 1) (n := n + 1) x a b y) = 0 := by
                    have : ¬ IsProper x := hx
                    have : ¬ IsProper (insert2 (q := 3) (m := m + 1) (n := n + 1) x a b y) := by
                      have : ¬ IsProper (snoc x a) := by
                        intro h; exact this (isProper_of_isProper_snoc (x := x) (a := a) h)
                      have : ¬ IsProper (snoc (snoc x a) b) := by
                        intro h; exact this (isProper_of_isProper_snoc (x := snoc x a) (a := b) h)
                      have : ¬ IsProper (append (snoc (snoc x a) b) y) :=
                        Word.not_isProper_append_left_of_not_isProper (q := 3)
                          (x := snoc (snoc x a) b) (y := y) this
                      simpa [Word.insert2, Word.append] using this
                    simpa [Word.insert2, Nat.add_assoc, Nat.one_add] using
                      (B_eq_zero_of_not_isProper (q := 3)
                        (x := insert2 (q := 3) (m := m + 1) (n := n + 1) x a b y)
                        (n := (m + 1) + 2 + n) this)
                  have hleft :
                      (∑ a : Fin 3, ∑ b : Fin 3, B (insert2 (q := 3) (m := m + 1) (n := n + 1) x a b y)) = 0 := by
                    simp [hterm]
                  simp [hleft, hx0]
  -- Close the induction with `k = m + n`.
  simpa using hk (m + n) (x := x) (y := y) rfl

end Word

end FiniteDependence.Coloring
