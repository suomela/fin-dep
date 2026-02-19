import FiniteDependence.Coloring.Combinatorics

/-!
# Deletion lemmas for inserted/concatenated words

This file collects technical lemmas about how `Word.erase` interacts with `Word.append`
and `Word.insert1`/`Word.insert2`.

These are used to expand the defining recursion of `Word.B` on composite words.
-/

open scoped BigOperators

namespace FiniteDependence.Coloring

namespace Word

variable {q m n : ℕ}

/-- Deleting an index in the right part of an appended word. -/
@[simp] lemma erase_append_natAdd (u : Word q m) (v : Word q (n + 1)) (i : Fin (n + 1)) :
    erase (q := q) (n := m + n) (append (q := q) (m := m) (n := n + 1) u v) (Fin.natAdd m i)
      = append (q := q) (m := m) (n := n) u (erase (q := q) (n := n) v i) := by
  ext j
  induction j using Fin.addCases with
  | left j =>
    have hcond : (Fin.castAdd n j).castSucc < Fin.natAdd m i := by
      -- Compare values: `j < m ≤ m + i`.
      simpa [Fin.lt_def] using Nat.lt_of_lt_of_le j.isLt (Nat.le_add_right m (i : ℕ))
    simp [erase, append, Fin.succAbove, hcond]
    simp [Fin.castSucc_castAdd]
  | right j =>
    by_cases hj : j.castSucc < i
    · simp [erase, append, Fin.succAbove, hj]
    · simp [erase, append, Fin.succAbove, hj, Fin.succ_natAdd]

/-- Deleting an index in the left part of an appended word.

Since the predecessor of `m + 1 + (n + 1)` is definitionally `(m + 1) + n`, the result is cast
to match the more natural type `m + (n + 1)`. -/
lemma erase_append_castAdd (u : Word q (m + 1)) (v : Word q (n + 1)) (i : Fin (m + 1)) :
    Word.cast (q := q) (by simp [Nat.add_assoc, Nat.one_add])
        (erase (q := q) (n := (m + 1) + n) (append (q := q) (m := m + 1) (n := n + 1) u v)
          (Fin.castAdd (n + 1) i))
      = append (q := q) (m := m) (n := n + 1) (erase (q := q) (n := m) u i) v := by
  classical
  -- Normalize the proof used in `Word.cast` so we can reason about the induced `Fin.cast`.
  have h : (m + 1) + n = m + (n + 1) := by
    simp [Nat.add_assoc, Nat.one_add]
  have hEq :
      (by simp [Nat.add_assoc, Nat.one_add] : (m + 1) + n = m + (n + 1)) = h :=
    Subsingleton.elim _ _
  ext j
  induction j using Fin.addCases with
  | left j =>
    -- Index in the left block.
    have hcastSucc :
        (Fin.cast h.symm (Fin.castAdd (n + 1) j)).castSucc = Fin.castAdd (n + 1) j.castSucc := by
      apply Fin.ext
      simp
    have hsucc :
        (Fin.cast h.symm (Fin.castAdd (n + 1) j)).succ = Fin.castAdd (n + 1) j.succ := by
      apply Fin.ext
      simp
    by_cases hj : j.castSucc < i
    · have hcond' : Fin.castAdd (n + 1) j.castSucc < Fin.castAdd (n + 1) i := by
        simpa [Fin.lt_def] using hj
      simp [erase, append, Word.cast, Fin.succAbove, hj, hcond', hcastSucc]
    · have hcond' : ¬ Fin.castAdd (n + 1) j.castSucc < Fin.castAdd (n + 1) i := by
        simpa [Fin.lt_def] using hj
      simp [erase, append, Word.cast, Fin.succAbove, hj, hcond', hcastSucc, hsucc]
  | right j =>
    -- Index in the right block: the `<` test in `succAbove` is always false, since the deleted
    -- index lies in the left block.
    have hcond' :
        ¬ (Fin.cast h.symm (Fin.natAdd m j)).castSucc < Fin.castAdd (n + 1) i := by
      have hij : (i : ℕ) ≤ m + (j : ℕ) :=
        Nat.le_trans (Nat.le_of_lt_succ i.isLt) (Nat.le_add_right m (j : ℕ))
      have : ¬ (m + (j : ℕ) < (i : ℕ)) := Nat.not_lt_of_ge hij
      simpa [Fin.lt_def] using this
    have hsucc :
        (Fin.cast h.symm (Fin.natAdd m j)).succ = Fin.natAdd (m + 1) j := by
      apply Fin.ext
      simp [Nat.add_assoc, Nat.add_left_comm, Nat.add_comm]
    simp [erase, append, Word.cast, Fin.succAbove, hcond', hsucc]

/-! ## Expanding `B` on an inserted word -/

lemma B_insert1_eq (x : Word q (m + 1)) (a : Fin q) (y : Word q (n + 1))
    (hxy : IsProper (insert1 (q := q) (m := m + 1) (n := n + 1) x a y)) :
    B (insert1 (q := q) (m := m + 1) (n := n + 1) x a y)
      = (∑ i : Fin (m + 1), B (insert1 (q := q) (m := m) (n := n + 1) (erase (n := m) x i) a y))
        + B (append (q := q) (m := m + 1) (n := n + 1) x y)
        + ∑ j : Fin (n + 1), B (insert1 (q := q) (m := m + 1) (n := n) x a (erase (n := n) y j)) := by
  classical
  -- Abbreviate the inserted word.
  let w : Word q (m + 1 + 1 + n + 1) :=
    insert1 (q := q) (m := m + 1) (n := n + 1) x a y

  have hB : B w = ∑ k : Fin (m + 1 + 1 + n + 1), B (erase w k) := by
    -- This is exactly the defining recursion for `B`.
    simpa [w] using (B_eq_sum_erase_of_isProper (q := q) (n := m + 1 + 1 + n) (x := w) hxy)

  -- Split the deletion sum into the left and right blocks of the appended word.
  have hsplit :
      (∑ k : Fin (m + 1 + 1 + n + 1), B (erase w k))
        = (∑ i : Fin (m + 1 + 1), B (erase w (Fin.castAdd (n + 1) i)))
          + ∑ j : Fin (n + 1), B (erase w (Fin.natAdd (m + 1 + 1) j)) := by
    simpa [Nat.add_assoc] using
      (Fin.sum_univ_add (f := fun k : Fin ((m + 1 + 1) + (n + 1)) => B (erase w k)))

  -- Split the left block into deletions in `x` and deletion of the inserted letter `a`.
  have hsplitLeft :
      (∑ i : Fin (m + 1 + 1), B (erase w (Fin.castAdd (n + 1) i)))
        = (∑ i : Fin (m + 1), B (erase w (Fin.castAdd (n + 1) i.castSucc)))
          + B (erase w (Fin.castAdd (n + 1) (Fin.last (m + 1)))) := by
    simpa [Nat.add_assoc] using
      (Fin.sum_univ_castSucc (f := fun i : Fin ((m + 1) + 1) => B (erase w (Fin.castAdd (n + 1) i))))

  -- Rewrite each deletion term using the `erase_append_*` lemmas.
  have hLeftTerm (i : Fin (m + 1)) :
      B (erase w (Fin.castAdd (n + 1) i.castSucc))
        = B (insert1 (q := q) (m := m) (n := n + 1) (erase (n := m) x i) a y) := by
    have hErase :=
      erase_append_castAdd (q := q) (m := m + 1) (n := n) (u := snoc x a) (v := y)
        (i := i.castSucc)
    have hBErase := congrArg (B (q := q)) hErase
    simpa [w, Word.insert1, Word.append] using hBErase

  have hMidTerm :
      B (erase w (Fin.castAdd (n + 1) (Fin.last (m + 1))))
        = B (append (q := q) (m := m + 1) (n := n + 1) x y) := by
    have hErase :=
      erase_append_castAdd (q := q) (m := m + 1) (n := n) (u := snoc x a) (v := y)
        (i := Fin.last (m + 1))
    have hBErase := congrArg (B (q := q)) hErase
    simpa [w, Word.insert1, Word.append] using hBErase

  have hRightTerm (j : Fin (n + 1)) :
      B (erase w (Fin.natAdd (m + 1 + 1) j))
        = B (insert1 (q := q) (m := m + 1) (n := n) x a (erase (n := n) y j)) := by
    have hErase :=
      erase_append_natAdd (q := q) (m := m + 1 + 1) (n := n) (u := snoc x a) (v := y) j
    have hBErase := congrArg (B (q := q)) hErase
    simpa [w, Word.insert1, Word.append] using hBErase

  -- Now combine everything.
  have hSumLeft :
      (∑ i : Fin (m + 1), B (erase w (Fin.castAdd (n + 1) i.castSucc)))
        = ∑ i : Fin (m + 1), B (insert1 (q := q) (m := m) (n := n + 1) (erase (n := m) x i) a y) := by
    simpa using Fintype.sum_congr
      (fun i : Fin (m + 1) => B (erase w (Fin.castAdd (n + 1) i.castSucc)))
      (fun i : Fin (m + 1) =>
        B (insert1 (q := q) (m := m) (n := n + 1) (erase (n := m) x i) a y))
      hLeftTerm

  have hSumRight :
      (∑ j : Fin (n + 1), B (erase w (Fin.natAdd (m + 1 + 1) j)))
        = ∑ j : Fin (n + 1), B (insert1 (q := q) (m := m + 1) (n := n) x a (erase (n := n) y j)) := by
    simpa using Fintype.sum_congr
      (fun j : Fin (n + 1) => B (erase w (Fin.natAdd (m + 1 + 1) j)))
      (fun j : Fin (n + 1) =>
        B (insert1 (q := q) (m := m + 1) (n := n) x a (erase (n := n) y j)))
      hRightTerm

  -- Finish with rewriting and associativity.
  have :
      B w
        = (∑ i : Fin (m + 1), B (insert1 (q := q) (m := m) (n := n + 1) (erase (n := m) x i) a y))
          + B (append (q := q) (m := m + 1) (n := n + 1) x y)
          + ∑ j : Fin (n + 1), B (insert1 (q := q) (m := m + 1) (n := n) x a (erase (n := n) y j)) := by
    -- Start from `hB`, then substitute the split sums and rewritten terms.
    calc
      B w = ∑ k : Fin (m + 1 + 1 + n + 1), B (erase w k) := hB
      _ = (∑ i : Fin (m + 1 + 1), B (erase w (Fin.castAdd (n + 1) i)))
            + ∑ j : Fin (n + 1), B (erase w (Fin.natAdd (m + 1 + 1) j)) := by
            simpa using hsplit
      _ = ((∑ i : Fin (m + 1), B (erase w (Fin.castAdd (n + 1) i.castSucc)))
              + B (erase w (Fin.castAdd (n + 1) (Fin.last (m + 1)))))
            + ∑ j : Fin (n + 1), B (erase w (Fin.natAdd (m + 1 + 1) j)) := by
            -- Replace the left sum using `hsplitLeft`.
            simpa [add_assoc] using congrArg (fun s => s + ∑ j : Fin (n + 1), B (erase w (Fin.natAdd (m + 1 + 1) j)))
              hsplitLeft
      _ = ((∑ i : Fin (m + 1), B (insert1 (q := q) (m := m) (n := n + 1) (erase (n := m) x i) a y))
              + B (append (q := q) (m := m + 1) (n := n + 1) x y))
            + ∑ j : Fin (n + 1), B (insert1 (q := q) (m := m + 1) (n := n) x a (erase (n := n) y j)) := by
            -- Rewrite each term.
            simp [hSumLeft, hMidTerm, hSumRight, add_assoc]
      _ = _ := by
            -- Reassociate to match the statement.
            simp [add_assoc]

  simpa [w] using this

/-- Expanding `B` on a word with two inserted letters.

This is the `q`-general analogue of equation (6) in Holroyd–Liggett (arXiv:1403.2448v4),
expressed using `Word.insert2`. -/
lemma B_insert2_eq (x : Word q (m + 1)) (a b : Fin q) (y : Word q (n + 1))
    (hxy : IsProper (insert2 (q := q) (m := m + 1) (n := n + 1) x a b y)) :
    B (insert2 (q := q) (m := m + 1) (n := n + 1) x a b y)
      = (∑ i : Fin (m + 1),
            B (insert2 (q := q) (m := m) (n := n + 1) (erase (n := m) x i) a b y))
        + B (insert1 (q := q) (m := m + 1) (n := n + 1) x b y)
        + B (insert1 (q := q) (m := m + 1) (n := n + 1) x a y)
        + ∑ j : Fin (n + 1),
            B (insert2 (q := q) (m := m + 1) (n := n) x a b (erase (n := n) y j)) := by
  classical
  -- Abbreviate the inserted word.
  let w : Word q ((m + 1) + 2 + (n + 1)) :=
    insert2 (q := q) (m := m + 1) (n := n + 1) x a b y

  have hB : B w = ∑ k : Fin ((m + 1) + 2 + (n + 1)), B (erase w k) := by
    simpa [w, Nat.add_assoc] using
      (B_eq_sum_erase_of_isProper (q := q) (n := (m + 1) + 2 + n) (x := w) hxy)

  -- Split the deletion sum into the left and right blocks of the appended word.
  have hsplit :
      (∑ k : Fin ((m + 1) + 2 + (n + 1)), B (erase w k))
        = (∑ i : Fin ((m + 1) + 2), B (erase w (Fin.castAdd (n + 1) i)))
          + ∑ j : Fin (n + 1), B (erase w (Fin.natAdd ((m + 1) + 2) j)) := by
    -- `((m+1)+2) + (n+1) = (m+1)+2+(n+1)`.
    simpa [Nat.add_assoc] using
      (Fin.sum_univ_add (f := fun k : Fin (((m + 1) + 2) + (n + 1)) => B (erase w k)))

  -- Rewrite the right-block deletions.
  have hRightTerm (j : Fin (n + 1)) :
      B (erase w (Fin.natAdd ((m + 1) + 2) j))
        = B (insert2 (q := q) (m := m + 1) (n := n) x a b (erase (n := n) y j)) := by
    have hErase :=
      erase_append_natAdd (q := q) (m := (m + 1) + 2) (n := n)
        (u := snoc (snoc x a) b) (v := y) j
    have hBErase := congrArg (B (q := q)) hErase
    simpa [w, Word.insert2, Word.insert1, Word.append, Nat.add_assoc, Nat.one_add] using hBErase

  -- Rewrite the left-block deletions to deletions in the left word `snoc (snoc x a) b`.
  have hLeftTerm (i : Fin ((m + 1) + 2)) :
      B (erase w (Fin.castAdd (n + 1) i))
        = B (append (q := q) (m := (m + 1) + 1) (n := n + 1)
              (erase (q := q) (n := (m + 1) + 1) (snoc (snoc x a) b) i) y) := by
    -- `snoc (snoc x a) b` has length `(m+1)+2 = (m+1+1)+1`.
    have hErase :=
      erase_append_castAdd (q := q) (m := (m + 1) + 1) (n := n)
        (u := snoc (snoc x a) b) (v := y) (i := i)
    have hBErase := congrArg (B (q := q)) hErase
    -- Remove the cast using `B_cast`.
    simpa [w, Word.insert2, Word.append, B_cast, Nat.add_assoc, Nat.one_add] using hBErase

  -- Now split the left-block sum into: deletions in `x`, deletion of `a`, deletion of `b`.
  have hLeftSplit :
      (∑ i : Fin ((m + 1) + 2), B (erase w (Fin.castAdd (n + 1) i)))
        = (∑ i : Fin (m + 1),
              B (insert2 (q := q) (m := m) (n := n + 1) (erase (n := m) x i) a b y))
          + B (insert1 (q := q) (m := m + 1) (n := n + 1) x b y)
          + B (insert1 (q := q) (m := m + 1) (n := n + 1) x a y) := by
    -- We identify each deletion in `snoc (snoc x a) b`:
    -- * deleting `b` gives `snoc x a` (hence `insert1 x a y`);
    -- * deleting `a` gives `snoc x b` (hence `insert1 x b y`);
    -- * deleting a position in `x` gives `snoc (snoc (erase x i) a) b` (hence `insert2 (erase x i) a b y`).
    let u : Word q ((m + 1) + 2) := snoc (snoc x a) b

    have hsum_castSucc :
        (∑ i : Fin ((m + 1) + 2), B (erase w (Fin.castAdd (n + 1) i)))
          = (∑ i : Fin ((m + 1) + 1), B (erase w (Fin.castAdd (n + 1) i.castSucc)))
            + B (erase w (Fin.castAdd (n + 1) (Fin.last ((m + 1) + 1)))) := by
      simpa [Nat.add_assoc] using
        (Fin.sum_univ_castSucc (f := fun i : Fin (((m + 1) + 1) + 1) => B (erase w (Fin.castAdd (n + 1) i))))

    -- The `i = last` term corresponds to deleting `b`.
    have hDelB :
        B (erase w (Fin.castAdd (n + 1) (Fin.last ((m + 1) + 1))))
          = B (insert1 (q := q) (m := m + 1) (n := n + 1) x a y) := by
      -- `erase u (last _) = snoc x a`.
      have hu : erase (q := q) (n := (m + 1) + 1) u (Fin.last ((m + 1) + 1)) = snoc x a := by
        simp [u]
      -- Rewrite using `hLeftTerm` at `i = last`.
      have h := hLeftTerm (i := Fin.last ((m + 1) + 1))
      -- Simplify the `append` term to `insert1 x a y`.
      simpa [w, Word.insert1, Word.insert2, Word.append, u, hu, Nat.add_assoc] using h

    -- Now split the remaining indices (castSucc) into deletions in `x` and deletion of `a`.
    have hsum_castSucc2 :
        (∑ i : Fin ((m + 1) + 1), B (erase w (Fin.castAdd (n + 1) i.castSucc)))
          = (∑ i : Fin (m + 1), B (erase w (Fin.castAdd (n + 1) i.castSucc.castSucc)))
            + B (erase w (Fin.castAdd (n + 1) ((Fin.last (m + 1)).castSucc))) := by
      -- Apply `Fin.sum_univ_castSucc` to the function on `Fin ((m+1)+1) = Fin (m+2)`.
      simpa [Nat.add_assoc] using
        (Fin.sum_univ_castSucc
          (f := fun i : Fin ((m + 1) + 1) => B (erase w (Fin.castAdd (n + 1) i.castSucc))))

    -- The special term corresponds to deleting `a`.
    have hDelA :
        B (erase w (Fin.castAdd (n + 1) ((Fin.last (m + 1)).castSucc)))
          = B (insert1 (q := q) (m := m + 1) (n := n + 1) x b y) := by
      -- `erase u (castSucc (last _))` deletes the second-to-last entry (the inserted `a`),
      -- leaving `snoc x b`.
      have hu : erase (q := q) (n := (m + 1) + 1) u ((Fin.last (m + 1)).castSucc) = snoc x b := by
        -- Delete the second-to-last entry: `erase_snoc_castSucc` then `erase_snoc_last`.
        simp [u]
      have h := hLeftTerm (i := (Fin.last (m + 1)).castSucc)
      simpa [w, Word.insert1, Word.insert2, Word.append, u, hu, Nat.add_assoc] using h

    -- The remaining sum corresponds to deletions in `x`.
    have hDelX (i : Fin (m + 1)) :
        B (erase w (Fin.castAdd (n + 1) i.castSucc.castSucc))
          = B (insert2 (q := q) (m := m) (n := n + 1) (erase (n := m) x i) a b y) := by
      -- Deleting within `u` at `i.castSucc.castSucc` deletes within the original `x`.
      have hu : erase (q := q) (n := (m + 1) + 1) u i.castSucc.castSucc = snoc (snoc (erase (n := m) x i) a) b := by
        -- Delete a position in `x`: apply `erase_snoc_castSucc` twice.
        simp [u]
      have h := hLeftTerm (i := i.castSucc.castSucc)
      simpa [w, Word.insert2, Word.append, u, hu, Nat.add_assoc] using h

    -- Combine the pieces, rewriting the outer sums using the above identifications.
    calc
      (∑ i : Fin ((m + 1) + 2), B (erase w (Fin.castAdd (n + 1) i)))
          = (∑ i : Fin ((m + 1) + 1), B (erase w (Fin.castAdd (n + 1) i.castSucc)))
              + B (erase w (Fin.castAdd (n + 1) (Fin.last ((m + 1) + 1)))) := by
                simpa using hsum_castSucc
      _ = ((∑ i : Fin (m + 1), B (erase w (Fin.castAdd (n + 1) i.castSucc.castSucc)))
              + B (erase w (Fin.castAdd (n + 1) ((Fin.last (m + 1)).castSucc))))
            + B (erase w (Fin.castAdd (n + 1) (Fin.last ((m + 1) + 1)))) := by
                rw [hsum_castSucc2]
      _ = ((∑ i : Fin (m + 1),
                B (insert2 (q := q) (m := m) (n := n + 1) (erase (n := m) x i) a b y))
            + B (insert1 (q := q) (m := m + 1) (n := n + 1) x b y))
            + B (insert1 (q := q) (m := m + 1) (n := n + 1) x a y) := by
                -- Rewrite each term.
                simp [hDelX, hDelA, hDelB, add_assoc]
      _ = _ := by
            ac_rfl

  -- Put everything together.
  have :
      B w
        = (∑ i : Fin (m + 1),
              B (insert2 (q := q) (m := m) (n := n + 1) (erase (n := m) x i) a b y))
          + B (insert1 (q := q) (m := m + 1) (n := n + 1) x b y)
          + B (insert1 (q := q) (m := m + 1) (n := n + 1) x a y)
          + ∑ j : Fin (n + 1),
              B (insert2 (q := q) (m := m + 1) (n := n) x a b (erase (n := n) y j)) := by
    calc
      B w = ∑ k : Fin ((m + 1) + 2 + (n + 1)), B (erase w k) := hB
      _ = (∑ i : Fin ((m + 1) + 2), B (erase w (Fin.castAdd (n + 1) i)))
            + ∑ j : Fin (n + 1), B (erase w (Fin.natAdd ((m + 1) + 2) j)) := by
            simpa [Nat.add_assoc] using hsplit
      _ = ((∑ i : Fin (m + 1),
                B (insert2 (q := q) (m := m) (n := n + 1) (erase (n := m) x i) a b y))
              + B (insert1 (q := q) (m := m + 1) (n := n + 1) x b y)
              + B (insert1 (q := q) (m := m + 1) (n := n + 1) x a y))
            + ∑ j : Fin (n + 1), B (insert2 (q := q) (m := m + 1) (n := n) x a b (erase (n := n) y j)) := by
            -- Rewrite the left block using `hLeftSplit` and the right block using `hRightTerm`.
            have hRight :
                (∑ j : Fin (n + 1), B (erase w (Fin.natAdd ((m + 1) + 2) j)))
                  = ∑ j : Fin (n + 1),
                      B (insert2 (q := q) (m := m + 1) (n := n) x a b (erase (n := n) y j)) := by
              refine Fintype.sum_congr _ _ ?_
              intro j
              exact hRightTerm j
            simp [hLeftSplit, hRight, add_assoc]
      _ = _ := by
            -- Reassociate.
            simp [add_assoc]

  simpa [w, Nat.add_assoc, add_assoc] using this

end Word

end FiniteDependence.Coloring
