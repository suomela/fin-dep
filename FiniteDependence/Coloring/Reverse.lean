import FiniteDependence.Coloring.Buildings
import Mathlib.Data.Fin.Rev
import Mathlib.Algebra.BigOperators.Fin

/-!
# Reversal of words

Some parts of the Holroyd–Liggett argument use symmetry between the left and right ends of a word.
In this development we derive left-end statements from right-end ones by reversing finite words.

The key result is that the recursively-defined function `Word.B` is invariant under reversal.
-/

open scoped BigOperators

namespace FiniteDependence.Coloring

namespace Word

variable {q n : ℕ}

/-- Reverse a word. -/
def reverse (x : Word q n) : Word q n :=
  fun i => x i.rev

@[simp] lemma reverse_apply (x : Word q n) (i : Fin n) : reverse x i = x i.rev := rfl

@[simp] lemma reverse_reverse (x : Word q n) : reverse (reverse x) = x := by
  ext i
  simp [reverse]

@[simp] lemma reverse_snoc {n : ℕ} (x : Word q n) (a : Fin q) :
    reverse (snoc x a) = cons a (reverse x) := by
  ext i
  cases i using Fin.cases with
  | zero =>
    -- `0.rev = last _`, so the appended symbol becomes the first one after reversal.
    simp [reverse, snoc, cons]
  | succ i =>
    -- Use `Fin.rev_succ` to reduce to the cast-succ case of `snoc`.
    simp [reverse, snoc, cons, Fin.rev_succ]

@[simp] lemma reverse_cons {n : ℕ} (a : Fin q) (x : Word q n) :
    reverse (cons a x) = snoc (reverse x) a := by
  ext i
  induction i using Fin.lastCases with
  | last =>
    -- `(last _).rev = 0`.
    simp [reverse, snoc, cons]
  | cast i =>
    -- Use `Fin.rev_castSucc`.
    simp [reverse, snoc, cons, Fin.rev_castSucc]

lemma isProper_reverse_iff {x : Word q n} : IsProper (reverse x) ↔ IsProper x := by
  classical
  cases n with
  | zero =>
    simp [IsProper]
  | succ n =>
    cases n with
    | zero =>
      -- Length `1`.
      simp [IsProper]
    | succ n =>
      -- Length `n + 2`.
      constructor
      · intro hx i
        -- Use the reversed adjacency index `i.rev`.
        have h := hx i.rev
        -- In `reverse x`, the adjacency at `i.rev` corresponds to the adjacency at `i` in `x`,
        -- but in the opposite order.
        have : x i.succ ≠ x i.castSucc := by
          simpa [reverse, Fin.rev_castSucc, Fin.rev_succ] using h
        exact (ne_comm).1 this
      · intro hx i
        have h := hx i.rev
        have : x i.succ.rev ≠ x i.castSucc.rev := by
          simpa [Fin.rev_castSucc, Fin.rev_succ] using h
        -- Rewrite back to `reverse x` and swap sides.
        exact (ne_comm).1 (by simpa [reverse] using this)

@[simp] lemma erase_reverse (x : Word q (n + 1)) (i : Fin (n + 1)) :
    erase (reverse x) i = reverse (erase x i.rev) := by
  ext j
  simp [erase, reverse, Fin.rev_succAbove]

@[simp] lemma B_reverse (x : Word q n) : B (reverse x) = B x := by
  classical
  induction n with
  | zero =>
    simp
  | succ n ih =>
    by_cases hx : IsProper x
    · have hx_rev : IsProper (reverse x) := (isProper_reverse_iff (x := x)).2 hx
      -- Expand `B` on both sides using the recursion and reindex the deletion sum by `Fin.rev`.
      have hsum :
          (∑ i : Fin (n + 1), B (erase x i.rev)) = ∑ i : Fin (n + 1), B (erase x i) := by
        -- `rev` is a permutation of `Fin (n+1)`.
        simpa using
          (Fintype.sum_equiv (e := Fin.revPerm (n := n + 1))
            (f := fun i : Fin (n + 1) => B (erase x i.rev))
            (g := fun i : Fin (n + 1) => B (erase x i))
            (h := fun i => rfl))
      calc
        B (reverse x)
            = ∑ i : Fin (n + 1), B (erase (reverse x) i) := by
                simp [B, hx_rev]
        _ = ∑ i : Fin (n + 1), B (reverse (erase x i.rev)) := by
              simp [erase_reverse]
        _ = ∑ i : Fin (n + 1), B (erase x i.rev) := by
              simp [ih]
        _ = ∑ i : Fin (n + 1), B (erase x i) := hsum
        _ = B x := by
              simp [B, hx]
    · have hx_rev : ¬ IsProper (reverse x) := by
        intro h; exact hx ((isProper_reverse_iff (x := x)).1 h)
      simp [B, hx, hx_rev]

end Word

end FiniteDependence.Coloring
