import FiniteDependence.Coloring.Buildings
import FiniteDependence.Coloring.Reverse
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Data.Nat.Choose.Basic

/-!
# Combinatorial identities for `B`

This file formalizes the identities used in the probabilistic construction.

At this stage we prove Proposition 10 of Holroyd–Liggett: a recursion for the total `B`-mass
obtained by appending one letter.

Later extensions will add Proposition 11 and the normalization constants.
-/

open scoped BigOperators

namespace FiniteDependence.Coloring

namespace Word

variable {q : ℕ}

private lemma not_isProper_snoc_of_not_isProper {n : ℕ} (x : Word q (n + 1)) (a : Fin q)
    (hx : ¬ IsProper x) : ¬ IsProper (snoc x a) := by
  intro hxa
  exact hx (isProper_of_isProper_snoc x a hxa)

/-! ## Proposition 10 -/

/-- Proposition 10 (Holroyd–Liggett): summing over the last letter. -/
theorem sum_B_snoc (hq : 2 ≤ q) :
    ∀ {n : ℕ} (x : Word q n),
      (∑ a : Fin q, B (snoc x a)) = (n * (q - 2) + q) * B x := by
  classical
  intro n
  induction n with
  | zero =>
    intro x
    -- Words of length `0` have `B = 1`, and all length-`1` words also have `B = 1`.
    simp [B, IsProper]
  | succ n ih =>
    intro x
    by_cases hx : IsProper x
    · -- Main (proper) case: follow the proof in the paper.
      let lastColor : Fin q := x (Fin.last n)
      let eraseSet : Finset (Fin q) := Finset.univ.erase lastColor

      have h_zero : B (snoc x lastColor) = 0 := by
        have : ¬ IsProper (snoc x lastColor) := not_isProper_snoc_self x
        simpa using (B_eq_zero_of_not_isProper (x := snoc x lastColor) (n := n + 1) this)

      have h_sum :
          (∑ a : Fin q, B (snoc x a)) = ∑ a ∈ eraseSet, B (snoc x a) := by
        -- Remove the zero contribution at `lastColor`.
        have hsum := (Finset.sum_erase_add (s := (Finset.univ : Finset (Fin q)))
          (a := lastColor) (f := fun a => B (snoc x a)) (Finset.mem_univ lastColor))
        have :
            (∑ a : Fin q, B (snoc x a))
              = (∑ a ∈ eraseSet, B (snoc x a)) + B (snoc x lastColor) := by
          simpa [eraseSet] using hsum.symm
        simpa [h_zero, add_comm, add_left_comm, add_assoc] using this

      have h_expand (a : Fin q) (ha : a ∈ eraseSet) :
          B (snoc x a)
            = (∑ i : Fin (n + 1), B (snoc (erase (n := n) x i) a)) + B x := by
        have ha_ne : a ≠ lastColor := (Finset.mem_erase.mp ha).1
        have hx' : IsProper (snoc x a) :=
          (isProper_snoc_iff (x := x) (a := a)).2 ⟨hx, by simpa [lastColor] using ha_ne.symm⟩
        have hB := B_eq_sum_erase_of_isProper (x := snoc x a) (n := n + 1) hx'
        -- Split the deletion sum into the last index and the remaining indices.
        -- Deleting the last index gives back `x`; deleting an earlier index gives
        -- `snoc (erase x i) a`.
        simp [hB, Fin.sum_univ_castSucc, erase_snoc_castSucc, erase_snoc_last]

      have card_eraseSet : eraseSet.card = q - 1 := by
        simp [eraseSet]
      have hxB : B x = ∑ i : Fin (n + 1), B (erase (n := n) x i) := by
        simpa using (B_eq_sum_erase_of_isProper (x := x) (n := n) hx)

      -- Expand the LHS sum over `eraseSet`.
      have hL :
          (∑ a : Fin q, B (snoc x a))
            = (∑ i : Fin (n + 1), ∑ a ∈ eraseSet, B (snoc (erase (n := n) x i) a))
              + eraseSet.card * B x := by
        -- Start from `h_sum`, then expand each term with `h_expand`.
        calc
          (∑ a : Fin q, B (snoc x a))
              = ∑ a ∈ eraseSet, B (snoc x a) := by
                  simp [h_sum]
          _ = ∑ a ∈ eraseSet,
                ((∑ i : Fin (n + 1), B (snoc (erase (n := n) x i) a)) + B x) := by
                refine Finset.sum_congr rfl ?_
                intro a ha
                simp [h_expand a ha]
          _ = (∑ a ∈ eraseSet, ∑ i : Fin (n + 1), B (snoc (erase (n := n) x i) a))
                + (∑ a ∈ eraseSet, B x) := by
                simp [Finset.sum_add_distrib]
          _ = (∑ i : Fin (n + 1), ∑ a ∈ eraseSet, B (snoc (erase (n := n) x i) a))
                + (∑ a ∈ eraseSet, B x) := by
                -- Swap the order of summation in the double sum.
                congr 1
                simpa using
                  (Finset.sum_comm (s := eraseSet) (t := (Finset.univ : Finset (Fin (n + 1))))
                    (f := fun a i => B (snoc (erase (n := n) x i) a)))
          _ = (∑ i : Fin (n + 1), ∑ a ∈ eraseSet, B (snoc (erase (n := n) x i) a))
                + eraseSet.card * B x := by
                -- The sum of a constant is `card * const`.
                simp

      -- Compute the double sum `∑ i, ∑ a∈eraseSet, ...` using the induction hypothesis.
      have hD :
          (∑ i : Fin (n + 1), ∑ a ∈ eraseSet, B (snoc (erase (n := n) x i) a)) + B x
            = (n * (q - 2) + q) * B x := by
        -- Split the sum over `i : Fin (n+1)` into `castSucc` and `last`.
        -- For `castSucc` indices, the missing term at `lastColor` has `B = 0`.
        -- For the last index, the missing term is exactly `B x`.
        have h_cast (i : Fin n) :
            (∑ a ∈ eraseSet, B (snoc (erase (n := n) x i.castSucc) a))
              = (n * (q - 2) + q) * B (erase (n := n) x i.castSucc) := by
          cases n with
          | zero =>
            exact i.elim0
          | succ n =>
            -- Let `w` be the word obtained by deleting position `i.castSucc`.
            let w : Word q (n + 1) := erase (n := n + 1) x i.castSucc
            have h_last_eq : w (Fin.last n) = lastColor := by
              -- Deleting a non-last index keeps the last element unchanged.
              simp [w, lastColor]
            have h_not : ¬ IsProper (snoc w lastColor) := by
              intro hP
              have hlast : w (Fin.last n) ≠ lastColor :=
                ((isProper_snoc_iff (x := w) (a := lastColor)).1 hP).2
              exact hlast (by simp [h_last_eq])
            have hB0 : B (snoc w lastColor) = 0 := by
              simpa using (B_eq_zero_of_not_isProper (x := snoc w lastColor) (n := n + 1) h_not)
            have hrestore :
                (∑ a : Fin q, B (snoc w a)) = ∑ a ∈ eraseSet, B (snoc w a) := by
              have hsum :=
                (Finset.sum_erase_add (s := (Finset.univ : Finset (Fin q))) (a := lastColor)
                  (f := fun a => B (snoc w a)) (Finset.mem_univ lastColor))
              have :
                  (∑ a : Fin q, B (snoc w a))
                    = (∑ a ∈ eraseSet, B (snoc w a)) + B (snoc w lastColor) := by
                simpa [eraseSet] using hsum.symm
              simpa [hB0] using this
            -- Apply the induction hypothesis.
            simpa [w, hrestore] using (ih (x := w))

        have h_last :
            (∑ a ∈ eraseSet, B (snoc (erase (n := n) x (Fin.last n)) a)) + B x
              = (n * (q - 2) + q) * B (erase (n := n) x (Fin.last n)) := by
          -- Add back the missing term `a = lastColor`, which equals `B x`.
          have h_missing :
              B (snoc (erase (n := n) x (Fin.last n)) lastColor) = B x := by
            -- Reinsert the last letter to get back `x`.
            simp [lastColor]
          have hsum := (Finset.sum_erase_add (s := (Finset.univ : Finset (Fin q)))
            (a := lastColor) (f := fun a => B (snoc (erase (n := n) x (Fin.last n)) a))
            (Finset.mem_univ lastColor))
          -- `sum (eraseSet) + B(snoc ... lastColor) = sum univ`.
          -- Replace the missing term by `B x` and apply the induction hypothesis.
          have : (∑ a ∈ eraseSet, B (snoc (erase (n := n) x (Fin.last n)) a)) + B x
              = ∑ a : Fin q, B (snoc (erase (n := n) x (Fin.last n)) a) := by
            simpa [eraseSet, h_missing] using hsum
          -- Now use `ih` on `erase x (last n)`.
          simpa [this] using (ih (x := erase (n := n) x (Fin.last n)))

        -- Put the pieces together using `Fin.sum_univ_castSucc`.
        -- Define `S i` as the inner sum.
        have hS :
            (∑ i : Fin (n + 1), ∑ a ∈ eraseSet, B (snoc (erase (n := n) x i) a)) + B x
              = (n * (q - 2) + q) * (∑ i : Fin (n + 1), B (erase (n := n) x i)) := by
          let c : Nat := n * (q - 2) + q
          let S : Fin (n + 1) → Nat :=
            fun i => ∑ a ∈ eraseSet, B (snoc (erase (n := n) x i) a)
          have h_split :
              (∑ i : Fin (n + 1), S i) + B x
                = (∑ i : Fin n, S i.castSucc) + (S (Fin.last n) + B x) := by
            calc
              (∑ i : Fin (n + 1), S i) + B x
                  = ((∑ i : Fin n, S i.castSucc) + S (Fin.last n)) + B x := by
                      simp [Fin.sum_univ_castSucc]
              _ = (∑ i : Fin n, S i.castSucc) + (S (Fin.last n) + B x) := by
                      ac_rfl
          have h_sum_cast :
              (∑ i : Fin n, S i.castSucc) = ∑ i : Fin n, c * B (erase (n := n) x i.castSucc) := by
            refine
              Fintype.sum_congr (fun i : Fin n => S i.castSucc)
                (fun i : Fin n => c * B (erase (n := n) x i.castSucc)) ?_
            intro i
            simpa [S, c] using h_cast i
          have h_last' : S (Fin.last n) + B x = c * B (erase (n := n) x (Fin.last n)) := by
            simpa [S, c] using h_last
          have hmul :
              (∑ i : Fin n, c * B (erase (n := n) x i.castSucc))
                = c * (∑ i : Fin n, B (erase (n := n) x i.castSucc)) := by
            simpa using
              (Finset.mul_sum (s := (Finset.univ : Finset (Fin n)))
                (f := fun i : Fin n => B (erase (n := n) x i.castSucc)) (a := c)).symm
          have hsum :
              (∑ i : Fin (n + 1), B (erase (n := n) x i))
                = (∑ i : Fin n, B (erase (n := n) x i.castSucc)) + B (erase (n := n) x (Fin.last n)) := by
            simpa using (Fin.sum_univ_castSucc (f := fun i : Fin (n + 1) => B (erase (n := n) x i)))
          -- Now compute by splitting over `i : Fin (n+1)` and using `h_cast`/`h_last`.
          calc
            (∑ i : Fin (n + 1), ∑ a ∈ eraseSet, B (snoc (erase (n := n) x i) a)) + B x
                = (∑ i : Fin (n + 1), S i) + B x := by
                    simp [S]
            _ = (∑ i : Fin n, S i.castSucc) + (S (Fin.last n) + B x) := by
                    simpa using h_split
            _ = (∑ i : Fin n, c * B (erase (n := n) x i.castSucc))
                  + c * B (erase (n := n) x (Fin.last n)) := by
                    rw [h_sum_cast, h_last']
            _ = (c * (∑ i : Fin n, B (erase (n := n) x i.castSucc)))
                  + c * B (erase (n := n) x (Fin.last n)) := by
                    rw [hmul]
            _ = c * ((∑ i : Fin n, B (erase (n := n) x i.castSucc)) + B (erase (n := n) x (Fin.last n))) := by
                    rw [← Nat.mul_add]
            _ = c * (∑ i : Fin (n + 1), B (erase (n := n) x i)) := by
                    exact congrArg (fun t => c * t) hsum.symm
            _ = (n * (q - 2) + q) * (∑ i : Fin (n + 1), B (erase (n := n) x i)) := by
                    simp [c]
        -- Replace the sum of erasures by `B x` (Lemma 9).
        simpa [hxB] using hS

      -- Finish by rewriting the double sum using `hD` and simplifying the arithmetic.
      have h_double :
          (∑ i : Fin (n + 1), ∑ a ∈ eraseSet, B (snoc (erase (n := n) x i) a))
            = (n * (q - 2) + q) * B x - B x := by
        have := congrArg (fun t => t - B x) hD
        simpa [Nat.add_sub_cancel] using this

      -- Rewrite `(q - 1) = (q - 2) + 1` using the assumption `2 ≤ q`.
      have hq_sub : q - 1 = (q - 2) + 1 := by
        have h1lt : 1 < q := lt_of_lt_of_le (by decide : 1 < 2) hq
        have hpos : 0 < q - 1 := Nat.sub_pos_of_lt h1lt
        have h1le : 1 ≤ q - 1 := Nat.succ_le_iff.2 hpos
        have := Nat.sub_add_cancel h1le
        -- `(q - 1) - 1 = q - 2`.
        simpa [Nat.sub_sub, Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using this.symm

      have hCpos : 1 ≤ n * (q - 2) + q := by
        have : 1 ≤ q := (by decide : 1 ≤ 2).trans hq
        exact this.trans (Nat.le_add_left _ _)
      have hBx_le : B x ≤ (n * (q - 2) + q) * B x := by
        simpa [one_mul] using Nat.mul_le_mul_right (B x) hCpos

      -- Now compute.
      calc
        (∑ a : Fin q, B (snoc x a))
            = (∑ i : Fin (n + 1), ∑ a ∈ eraseSet, B (snoc (erase (n := n) x i) a))
                + eraseSet.card * B x := hL
        _ = ((n * (q - 2) + q) * B x - B x) + eraseSet.card * B x := by
              simp [h_double]
        _ = ((n * (q - 2) + q) * B x - B x) + ((q - 2) * B x + B x) := by
              -- Expand `eraseSet.card * B x` as `(q-2)*B x + B x`.
              -- Use `card_eraseSet` and `hq_sub`.
              simp [card_eraseSet, hq_sub, Nat.add_mul, Nat.add_assoc, Nat.add_comm]
        _ = ((n * (q - 2) + q) * B x - B x + B x) + (q - 2) * B x := by
              ac_rfl
        _ = (n * (q - 2) + q) * B x + (q - 2) * B x := by
              simp [Nat.sub_add_cancel hBx_le]
        _ = ((n * (q - 2) + q) + (q - 2)) * B x := by
              symm
              simp [Nat.add_mul, Nat.add_left_comm, Nat.add_comm]
        _ = (Nat.succ n * (q - 2) + q) * B x := by
              -- `Nat.succ n * (q-2) = n*(q-2) + (q-2)`.
              simp [Nat.succ_mul, Nat.add_left_comm, Nat.add_comm]
    · -- Non-proper case: everything is `0`.
      have hxB : B x = 0 := B_eq_zero_of_not_isProper (x := x) (n := n) hx
      have hxa (a : Fin q) : B (snoc x a) = 0 := by
        have : ¬ IsProper (snoc x a) := not_isProper_snoc_of_not_isProper x a hx
        exact B_eq_zero_of_not_isProper (x := snoc x a) (n := n + 1) this
      simp [hxB, hxa]

/-! ## A left-end variant of Proposition 10 -/

/-- A version of Proposition 10 that sums over the *first* letter. -/
theorem sum_B_cons (hq : 2 ≤ q) :
    ∀ {n : ℕ} (x : Word q n),
      (∑ a : Fin q, B (cons a x)) = (n * (q - 2) + q) * B x := by
  classical
  intro n x
  -- Reverse the word and use `sum_B_snoc`.
  have :
      (∑ a : Fin q, B (cons a x)) = ∑ a : Fin q, B (snoc (reverse x) a) := by
    -- `B (cons a x) = B (reverse (cons a x)) = B (snoc (reverse x) a)`.
    refine
      Fintype.sum_congr (fun a : Fin q => B (cons a x))
        (fun a : Fin q => B (snoc (reverse x) a)) ?_
    intro a
    simpa [Word.reverse_cons] using (B_reverse (x := cons a x)).symm
  -- Apply Proposition 10 to the reversed word and rewrite `B (reverse x) = B x`.
  simpa [this] using (sum_B_snoc (q := q) hq (x := reverse x))

end Word

end FiniteDependence.Coloring
