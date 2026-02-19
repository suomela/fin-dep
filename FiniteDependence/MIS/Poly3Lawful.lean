import FiniteDependence.MIS.Poly3
import Std.Data.TreeMap.Lemmas

namespace FiniteDependence.MIS

namespace Poly3

open Std

/-!
Auxiliary ordering/decidable instances for `Poly3.Monom`.

These are used only in proof files (e.g. evaluation lemmas) that reason about the
`Std.TreeMap`-based normalization in `Poly3.normalize`.
-/

lemma compare_def (a b : Monom) :
    compare a b =
      match compare a.pExp b.pExp with
      | .eq =>
          match compare a.tExp b.tExp with
          | .eq => compare a.uExp b.uExp
          | o => o
      | o => o := by
  rfl

instance : Std.ReflOrd Monom := by
  -- Lexicographic composition of three reflexive comparisons is reflexive.
  -- `infer_instance` works once we rewrite `compare` in terms of `compareLex/compareOn`.
  change Std.ReflCmp (fun a b : Monom =>
    compareLex (compareOn Monom.pExp)
      (compareLex (compareOn Monom.tExp) (compareOn Monom.uExp)) a b)
  infer_instance

instance : Std.OrientedOrd Monom := by
  change Std.OrientedCmp (fun a b : Monom =>
    compareLex (compareOn Monom.pExp)
      (compareLex (compareOn Monom.tExp) (compareOn Monom.uExp)) a b)
  infer_instance

instance : Std.TransOrd Monom := by
  change Std.TransCmp (fun a b : Monom =>
    compareLex (compareOn Monom.pExp)
      (compareLex (compareOn Monom.tExp) (compareOn Monom.uExp)) a b)
  infer_instance

instance : Std.LawfulEqOrd Monom where
  eq_of_compare {a b} h := by
    -- Unfold the lexicographic comparison and read off component equalities.
    -- The `compareLex_eq_eq` lemma decomposes `compareLex` equalities.
    have hp : compare a.pExp b.pExp = .eq := by
      -- `compare` for `Monom` compares `pExp` first.
      -- If the overall comparison is `.eq`, so is the first-stage comparison.
      cases hpb : compare a.pExp b.pExp with
      | lt =>
          -- then `compare a b = .lt`, contradiction
          have : compare a b = .lt := by simp [compare_def, hpb]
          cases (this.symm.trans h)
      | gt =>
          have : compare a b = .gt := by simp [compare_def, hpb]
          cases (this.symm.trans h)
      | eq =>
          rfl
    have ht : compare a.tExp b.tExp = .eq := by
      -- Once `pExp` compares equal, the result is the comparison of `tExp/uExp`.
      cases htb : compare a.tExp b.tExp with
      | lt =>
          have : compare a b = .lt := by simp [compare_def, hp, htb]
          cases (this.symm.trans h)
      | gt =>
          have : compare a b = .gt := by simp [compare_def, hp, htb]
          cases (this.symm.trans h)
      | eq =>
          rfl
    have hu : compare a.uExp b.uExp = .eq := by
      -- With `pExp` and `tExp` comparing equal, the full comparison is the `uExp` comparison.
      simpa [compare_def, hp, ht] using h

    have hp' : a.pExp = b.pExp := Std.LawfulEqOrd.eq_of_compare hp
    have ht' : a.tExp = b.tExp := Std.LawfulEqOrd.eq_of_compare ht
    have hu' : a.uExp = b.uExp := Std.LawfulEqOrd.eq_of_compare hu
    -- Assemble the record equality.
    cases a
    cases b
    cases hp'
    cases ht'
    cases hu'
    rfl

/-!
For `Std.TreeMap.toList_insert_perm` we need a boolean equality on keys plus the
lawfulness relationship between `compare` and that boolean equality.

We use the straightforward `DecidableEq`-based boolean equality.
-/

instance : BEq Monom where
  beq a b := decide (a = b)

instance : LawfulBEq Monom where
  eq_of_beq {a b} := by
    simp [BEq.beq]
  rfl {a} := by
    simp [BEq.beq]

-- With `LawfulEqOrd` + `LawfulBEq`, we get `LawfulBEqCmp compare` via core instances.

end Poly3

end FiniteDependence.MIS
