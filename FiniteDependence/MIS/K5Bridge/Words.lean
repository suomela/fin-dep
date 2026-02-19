import Mathlib

namespace FiniteDependence.MIS

/-!
Utilities for treating the `K5Data` words (stored as `String`s like `"0010101"`) as the
`Fin n → Bool` words used in the State cylinder sets.
-/

namespace K5Bridge

open scoped BigOperators

/-- Interpret a binary string (with characters `'0'`/`'1'`) as a word `Fin s.length → Bool`. -/
def wordOfString (s : String) : Fin s.length → Bool :=
  fun i =>
    let c :=
      s.toList.get ⟨i.1, by
        -- `String.get` uses byte positions; we instead index into `toList`.
        simpa [String.length_toList] using i.2
      ⟩
    decide (c = '1')

lemma wordOfString_apply (s : String) (i : Fin s.length) :
    wordOfString s i =
      decide (s.toList.get ⟨i.1, by simpa [String.length_toList] using i.2⟩ = '1') := by
  rfl

end K5Bridge

end FiniteDependence.MIS
