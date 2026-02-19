import FiniteDependence.Coloring.Words
import Mathlib.Algebra.BigOperators.Fin

/-!
# The function `B`

In the Holroyd–Liggett construction, `B(x)` is the number of *proper buildings* of a finite word
`x`. The key combinatorial fact is the recursion (Lemma 9 in the paper): for a proper word `x`,
`B(x)` equals the sum of `B` over the words obtained by deleting one symbol.

For the purposes of the probabilistic construction, it is convenient to take this recursion as
the definition of `B`. Later files prove the identities needed to build finitely dependent
colorings.
-/

open scoped BigOperators

namespace FiniteDependence.Coloring

namespace Word

variable {q : ℕ}

/-- The function `B` from the paper, defined by recursion on the word length. -/
def B : ∀ {n : ℕ}, Word q n → ℕ
  | 0, _ => 1
  | n + 1, x =>
      if _ : IsProper x then
        ∑ i : Fin (n + 1), B (erase x i)
      else 0

@[simp] lemma B_nil {x : Word q 0} : B x = 1 := by
  simp [B]

lemma B_eq_sum_erase_of_isProper {n : ℕ} (x : Word q (n + 1)) (hx : IsProper x) :
    B x = ∑ i : Fin (n + 1), B (erase x i) := by
  simp [B, hx]

lemma B_eq_zero_of_not_isProper {n : ℕ} (x : Word q (n + 1)) (hx : ¬ IsProper x) :
    B x = 0 := by
  simp [B, hx]

@[simp] lemma B_cast {m n : ℕ} (h : m = n) (x : Word q m) :
    B (q := q) (Word.cast (q := q) h x) = B x := by
  cases h
  simp

end Word

end FiniteDependence.Coloring
