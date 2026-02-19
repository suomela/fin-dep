import FiniteDependence.MIS.K5Data.Defs
import FiniteDependence.MIS.Model

namespace FiniteDependence.MIS

/-!
Facts about the `K5Data.allowedWords` enumeration, specialized to genuine MIS configurations.

The only property we need for the k=5 bridge is:

* for any `ω : State` and any `L ≥ 1`, the length-`L` block of `ω` at position `a` corresponds to
  a string in `K5Data.allowedWords L`.

This is proved directly from the MIS local constraints (`11` and `000`) and the one-step
extension rule used to build `allowedWords`.
-/

namespace K5Bridge

open K5Data

namespace Model

open FiniteDependence.MIS.Model

noncomputable section

/-- The `n`-bit string representing the block `ω[a..a+n)` (as `'0'`/`'1'` characters). -/
def blockString (a : ℤ) : Nat → FiniteDependence.MIS.State → String
  | 0, _ => ""
  | n + 1, ω =>
      (blockString a n ω).push (if ω.1 (a + Int.ofNat n) then '1' else '0')

lemma blockString_length (a : ℤ) (n : Nat) (ω : FiniteDependence.MIS.State) :
    (blockString a n ω).length = n := by
  induction n with
  | zero =>
      simp [blockString]
  | succ n ih =>
      simp [blockString, ih, String.length_push, Nat.add_assoc]

private lemma iterate_succ_apply {α : Type} (f : α → α) (n : Nat) (x : α) :
    Nat.iterate f (n + 1) x = f (Nat.iterate f n x) := by
  induction n generalizing x with
  | zero =>
      simp [Nat.iterate]
  | succ n ih =>
      -- Unfold both sides once and use the induction hypothesis on `f x`.
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
  -- `allowedWords (n+1) = iterate extendWords n base`, `allowedWords (n+2) = iterate extendWords (n+1) base`.
  -- Use `iterate_succ_apply` to commute the final application of `extendWords`.
  simp [K5Data.allowedWords, hn1, hn2, iterate_succ_apply, Nat.add_assoc, Nat.add_left_comm, Nat.add_comm]

lemma blockString_mem_allowedWords (ω : FiniteDependence.MIS.State) (a : ℤ) :
    ∀ n : Nat, blockString a (n + 1) ω ∈ (K5Data.allowedWords (n + 1)).toList := by
  intro n
  induction n with
  | zero =>
      -- Length 1: `allowedWords 1 = ["0","1"]`.
      cases h0 : ω.1 a with
      | false =>
          have hstr : blockString a 1 ω = "0" := by
            simp [blockString, h0]
            native_decide
          simpa [K5Data.allowedWords, hstr]
      | true =>
          have hstr : blockString a 1 ω = "1" := by
            simp [blockString, h0]
            native_decide
          simpa [K5Data.allowedWords, hstr]
  | succ n ih =>
      -- Step: `allowedWords (n+2) = extendWords (allowedWords (n+1))`.
      have hprev :
          blockString a (n + 1) ω ∈ (K5Data.allowedWords (n + 1)).toList := ih

      have hstepWords :
          blockString a (n + 2) ω ∈ (K5Data.extendWords (K5Data.allowedWords (n + 1))).toList := by
        -- `extendWords` is `toArray` of a `flatMap`; rewrite membership in the resulting list.
        have :
            blockString a (n + 2) ω ∈
              (K5Data.allowedWords (n + 1)).toList.flatMap (fun w => K5Data.extensions w) := by
          -- Witness the previous prefix word.
          refine List.mem_flatMap.2 ?_
          refine ⟨blockString a (n + 1) ω, hprev, ?_⟩
          -- Show the correct one-step extension is one of `extensions`.
          -- Write `s` for the length-(n+1) prefix string and `cNext` for the next character.
          set s : String := blockString a (n + 1) ω
          set cNext : Char := if ω.1 (a + Int.ofNat (n + 1)) then '1' else '0'
          have hs : blockString a (n + 1) ω = s := rfl
          have hsn : blockString a (n + 2) ω = s.push cNext := by
            simp [blockString, s, cNext, Nat.add_assoc, Nat.add_left_comm, Nat.add_comm]

          -- Case split on the last bit of `s`, i.e. `ω[a+n]`.
          cases hlast : ω.1 (a + Int.ofNat n) with
          | false =>
              -- Then `s` ends with `'0'`. If `n=0` we are in the default branch of `extensions`.
              cases n with
              | zero =>
                  -- `s` has length 1, so `extensions s` is `[s0,s1]`.
                  -- Membership is immediate.
                  have hs0 : s = "0" := by
                    -- `hlast` tells us the only bit of `s` is `0`.
                    have hlast0 : ω.1 a = false := by
                      simpa using hlast
                    have : blockString a 1 ω = "0" := by
                      simp [blockString, hlast0]
                      native_decide
                    simpa [s] using this
                  -- Split on the next bit; `extensions s` contains both options.
                  cases hnext : ω.1 (a + 1) with
                  | false =>
                      have hc : cNext = '0' := by simp [cNext, hnext]
                      -- Everything is now concrete.
                      simpa [hs0, hsn, hc] using
                        (by
                          native_decide :
                            ("0".push '0') ∈ (K5Data.extensions "0"))
                  | true =>
                      have hc : cNext = '1' := by simp [cNext, hnext]
                      simpa [hs0, hsn, hc] using
                        (by
                          native_decide :
                            ("0".push '1') ∈ (K5Data.extensions "0"))
              | succ n =>
                  -- Now `s` has length ≥ 2; inspect the previous bit `ω[a+(n-1)]`.
                  cases hprevBit : ω.1 (a + Int.ofNat n) with
                  | false =>
                      -- Last two bits are `00`, so the next bit is forced to `1`.
                      have hforced : ω.1 (a + Int.ofNat (n + 2)) = true := by
                        -- Apply `twoZeros_next_true` at position `a+n`.
                        have h0 : ω.1 (a + Int.ofNat n) = false := by simpa using hprevBit
                        have h1' : ω.1 ((a + Int.ofNat n) + 1) = false := by
                          -- This is the bit at `a + (n+1)`, which is our `hlast` case.
                          simpa [add_assoc, add_left_comm, add_comm] using hlast
                        have ht : ω.1 ((a + Int.ofNat n) + 2) = true :=
                          twoZeros_next_true ω (i := a + Int.ofNat n) h0 h1'
                        -- Rewrite `(a+n)+2` as `a+(n+2)`.
                        simpa [add_assoc, add_left_comm, add_comm] using ht
                      have hforced' : ω.1 (a + (↑n + 1 + 1)) = true := by
                        simpa [Int.ofNat_eq_natCast] using hforced
                      have hcNext : cNext = '1' := by
                        simp [cNext, hforced']
                      have hprevBit' : ω.1 (a + (↑n : ℤ)) = false := by
                        simpa [Int.ofNat_eq_natCast] using hprevBit
                      have hlast' : ω.1 (a + (↑n + 1)) = false := by
                        simpa [Int.ofNat_eq_natCast] using hlast
                      -- In this branch, the last two bits of `s` are `00`, so `extensions s = [s.push '1']`.
                      have hrev :
                          s.toList.reverse = '0' :: '0' :: (blockString a n ω).toList.reverse := by
                        -- Unfold `s = blockString a (n+2) ω` twice and compute `toList.reverse`.
                        -- (The only facts we use are `hlast`, `hprevBit`, and the `push` representation.)
                        simp [s, blockString, hlast', hprevBit', String.toList_push, List.reverse_append,
                          List.append_assoc]
                      have hext : K5Data.extensions s = [s.push '1'] := by
                        simp [K5Data.extensions, hrev]
                      -- Now `blockString a (n+2) ω` is exactly `s.push '1'`.
                      simpa [hsn, hcNext, hext]
                  | true =>
                      -- Previous bit is `1`, so we are in the default branch and both extensions are allowed.
                      have hprevBit' : ω.1 (a + (↑n : ℤ)) = true := by
                        simpa [Int.ofNat_eq_natCast] using hprevBit
                      have hlast' : ω.1 (a + (↑n + 1)) = false := by
                        simpa [Int.ofNat_eq_natCast] using hlast
                      have hrev :
                          s.toList.reverse = '0' :: '1' :: (blockString a n ω).toList.reverse := by
                        simp [s, blockString, hlast', hprevBit', String.toList_push, List.reverse_append,
                          List.append_assoc]
                      have hext : K5Data.extensions s = [s.push '0', s.push '1'] := by
                        simp [K5Data.extensions, hrev]
                      cases hnext : ω.1 (a + Int.ofNat (n + 2)) with
                      | false =>
                          have hnext' : ω.1 (a + (↑n + 1 + 1)) = false := by
                            simpa [Int.ofNat_eq_natCast] using hnext
                          have hc : cNext = '0' := by simp [cNext, hnext']
                          simpa [hsn, hext, hc]
                      | true =>
                          have hnext' : ω.1 (a + (↑n + 1 + 1)) = true := by
                            simpa [Int.ofNat_eq_natCast] using hnext
                          have hc : cNext = '1' := by simp [cNext, hnext']
                          simpa [hsn, hext, hc]
          | true =>
              -- If the last bit is `1`, State forces the next bit to be `0`.
              have hforced : ω.1 (a + Int.ofNat (n + 1)) = false := by
                have h1 : ω.1 (a + Int.ofNat n) = true := by simpa using hlast
                have ht : ω.1 ((a + Int.ofNat n) + 1) = false :=
                  true_next_false ω (i := a + Int.ofNat n) h1
                simpa [add_assoc, add_left_comm, add_comm] using ht
              have hforced' : ω.1 (a + (↑n + 1)) = false := by
                simpa [Int.ofNat_eq_natCast] using hforced
              have hcNext : cNext = '0' := by
                simp [cNext, hforced']
              have hlast' : ω.1 (a + (↑n : ℤ)) = true := by
                simpa [Int.ofNat_eq_natCast] using hlast
              have hrev : s.toList.reverse = '1' :: (blockString a n ω).toList.reverse := by
                simp [s, blockString, hlast', String.toList_push, List.reverse_append, List.append_assoc]
              have hext : K5Data.extensions s = [s.push '0'] := by
                simp [K5Data.extensions, hrev]
              simpa [hsn, hcNext, hext]

        -- Convert the `flatMap` membership back to an `Array` membership.
        -- `extendWords` is defined as `toArray` of this `flatMap`.
        simpa [K5Data.extendWords, List.toList_toArray] using this

      -- Finish by rewriting `allowedWords (n+2)` as `extendWords (allowedWords (n+1))`.
      simpa [allowedWords_succ_succ] using hstepWords

end

end Model

end K5Bridge

end FiniteDependence.MIS
