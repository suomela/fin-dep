import FiniteDependence.MIS.K5Bridge.PrefixSums

namespace FiniteDependence.MIS

/-!
Reusable measure-theoretic lemmas for the `k = 5` bridge step systems.

The linear step systems in `K5Data` include constraints of the form

`K5Data.RhsDesc.prod m x n y`

which encode the `5`-dependence identity (with a `5`-site gap):

`P(cylStr 0 x) * P(cylStr 0 y) = ∑_{w} P(cylStr 0 w)`,

where the sum ranges over all allowed length-`(m+5+n)` words `w` whose prefix of length `m`
is `x` and whose suffix of length `n` starts at position `m+5` (equivalently, dropping the first
`m+5` bits yields `y`).
-/

namespace K5Bridge

open MeasureTheory Set
open scoped BigOperators ProbabilityTheory

namespace Model

open FiniteDependence.MIS.Model

noncomputable section

/-! ### String helpers -/

/-- Drop the first `k` bits from a string, implemented via `toList.drop`. -/
def suffixFrom (s : String) (k : Nat) : String :=
  String.ofList (s.toList.drop k)

/-! ### Stationarity: shifting cylinders by a natural amount -/

theorem Stationary.prob_cylStr_add_nat {μ : Measure FiniteDependence.MIS.State} [IsProbabilityMeasure μ]
    (hμ : FiniteDependence.MIS.Model.Stationary μ) (a : ℤ) (n : Nat) (s : String) :
    FiniteDependence.MIS.Model.prob μ (cylStr (a := a + n) s) =
      FiniteDependence.MIS.Model.prob μ (cylStr (a := a) s) := by
  induction n generalizing a with
  | zero =>
      simp
  | succ n ih =>
      have h1 :
          FiniteDependence.MIS.Model.prob μ (cylStr (a := a + (n + 1)) s) =
            FiniteDependence.MIS.Model.prob μ (cylStr (a := a + n) s) := by
        simpa [Nat.add_assoc, Nat.cast_add, add_assoc] using
          (K5Bridge.Model.Stationary.prob_cylStr_succ (μ := μ) hμ (a := a + n) (s := s))
      simpa [Nat.add_assoc, Nat.cast_add, add_assoc] using h1.trans (ih (a := a))

/-! ### The k=5 “product” identity -/

private lemma natAbs_sub_eq_sub_of_le {a b : Nat} (hle : a ≤ b) :
    Int.natAbs ((a : ℤ) - (b : ℤ)) = b - a := by
  have hsub : (Int.ofNat (b - a) : ℤ) = (b : ℤ) - (a : ℤ) := by
    exact (Int.ofNat_sub (m := a) (n := b) hle)
  have hneg : ((a : ℤ) - (b : ℤ)) = -((b : ℤ) - (a : ℤ)) := by
    simp [sub_eq_add_neg, add_comm]
  have h1 : Int.natAbs ((a : ℤ) - (b : ℤ)) = Int.natAbs (-((b : ℤ) - (a : ℤ))) := by
    simpa using congrArg Int.natAbs hneg
  have h2 : Int.natAbs (-((b : ℤ) - (a : ℤ))) = Int.natAbs ((b : ℤ) - (a : ℤ)) := by
    simpa using (Int.natAbs_neg ((b : ℤ) - (a : ℤ)))
  calc
    Int.natAbs ((a : ℤ) - (b : ℤ)) = Int.natAbs ((b : ℤ) - (a : ℤ)) := by
      simpa [h1] using h2
    _ = b - a := by
      rw [← hsub]
      rfl

private lemma sep_gap5 (m n : Nat) :
    ∀ i : Fin m, ∀ j : Fin n,
      Int.natAbs (((0 : ℤ) + Int.ofNat i.1) - ((m + 5 : ℤ) + Int.ofNat j.1)) > 5 := by
  intro i j
  cases m with
  | zero =>
      exact (Fin.elim0 i)
  | succ m =>
      have hrew :
          Int.natAbs ((0 + Int.ofNat i.1) - ((Nat.succ m + 5 : ℤ) + Int.ofNat j.1)) =
            Int.natAbs ((i.1 : ℤ) - ((Nat.succ m + 5 + j.1 : Nat) : ℤ)) := by
        simp [Nat.cast_add, add_assoc, add_left_comm, add_comm]

      have hle : i.1 ≤ Nat.succ m + 5 + j.1 := by
        have hi_le : i.1 ≤ m := Nat.le_of_lt_succ i.2
        have hm_le : m ≤ m + 6 + j.1 := by
          simpa [Nat.add_assoc] using (Nat.le_add_right m (6 + j.1))
        have hm_le' : m ≤ Nat.succ m + 5 + j.1 := by
          simpa [Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using hm_le
        exact le_trans hi_le hm_le'

      have habs :
          Int.natAbs ((i.1 : ℤ) - ((Nat.succ m + 5 + j.1 : Nat) : ℤ)) =
            (Nat.succ m + 5 + j.1) - i.1 :=
        natAbs_sub_eq_sub_of_le hle

      have hi_le : i.1 ≤ m := Nat.le_of_lt_succ i.2
      have hmono : (m + 6) - m ≤ (m + 6) - i.1 := Nat.sub_le_sub_left hi_le (m + 6)
      have hbase : (m + 6) - m = 6 := by
        simpa [Nat.add_assoc] using (Nat.add_sub_cancel m 6)
      have h1 : 6 ≤ (m + 6) - i.1 := by
        simpa [hbase] using hmono
      have hj : m + 6 ≤ m + 6 + j.1 := by
        simpa [Nat.add_assoc] using (Nat.le_add_right (m + 6) j.1)
      have h2 : (m + 6) - i.1 ≤ (m + 6 + j.1) - i.1 := Nat.sub_le_sub_right hj i.1
      have hdist0 : 6 ≤ (m + 6 + j.1) - i.1 := le_trans h1 h2
      have hdist : 6 ≤ (Nat.succ m + 5 + j.1) - i.1 := by
        simpa [Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using hdist0
      have hgt : (Nat.succ m + 5 + j.1) - i.1 > 5 := lt_of_lt_of_le (by decide : 5 < 6) hdist

      have hfinal :
          Int.natAbs ((0 + Int.ofNat i.1) - ((Nat.succ m + 5 : ℤ) + Int.ofNat j.1)) =
            (Nat.succ m + 5 + j.1) - i.1 := by
        calc
          Int.natAbs ((0 + Int.ofNat i.1) - ((Nat.succ m + 5 : ℤ) + Int.ofNat j.1)) =
              Int.natAbs ((i.1 : ℤ) - ((Nat.succ m + 5 + j.1 : Nat) : ℤ)) := hrew
          _ = (Nat.succ m + 5 + j.1) - i.1 := habs

      -- Rewrite the goal using `hfinal`.
      rw [hfinal]
      exact hgt

/--
For a stationary 5-dependent State measure, the probability of seeing `x` and `y` separated by 5
sites factors, and the intersection event can be expanded as a disjoint union of length-`(m+5+n)`
allowed cylinders.

This is the semantic content behind `RhsDesc.prod m x n y`.
-/
theorem prob_prod_gap5 {μ : Measure FiniteDependence.MIS.State} [IsProbabilityMeasure μ]
    (hstat : Stationary μ) (hdep : KDependent 5 μ)
    {m n : Nat} {x y : String}
    (hx01 : Is01String x) (hy01 : Is01String y) (hxLen : x.length = m) (hyLen : y.length = n) :
    FiniteDependence.MIS.Model.prob μ (cylStr (a := (0 : ℤ)) x) *
        FiniteDependence.MIS.Model.prob μ (cylStr (a := (0 : ℤ)) y) =
      ∑ w ∈ (allowedWordsFinset (m + 5 + n)).filter (fun w => prefixOf w m = x ∧ suffixFrom w (m + 5) = y),
        FiniteDependence.MIS.Model.prob μ (cylStr (a := (0 : ℤ)) w) := by
  classical
  -- Independence between `{0..m-1}` and `{m+5..m+5+n-1}`.
  have hind0 :
      FiniteDependence.MIS.Model.prob μ (cylStr (a := (0 : ℤ)) x ∩ cylStr (a := (x.length + 5 : ℤ)) y) =
        FiniteDependence.MIS.Model.prob μ (cylStr (a := (0 : ℤ)) x) *
          FiniteDependence.MIS.Model.prob μ (cylStr (a := (x.length + 5 : ℤ)) y) := by
    have hsep' : ∀ i : Fin x.length, ∀ j : Fin y.length,
        Int.natAbs ((0 + Int.ofNat i.1) - ((x.length + 5 : ℤ) + Int.ofNat j.1)) > 5 :=
      sep_gap5 (m := x.length) (n := y.length)
    simpa [cylStr] using
      (FiniteDependence.MIS.Model.KDependent.prob_inter_cyl_eq_mul (μ := μ) (k := 5)
        (m := x.length) (n := y.length) (a := (0 : ℤ)) (b := (x.length + 5 : ℤ)) hdep hsep'
        (K5Bridge.wordOfString x) (K5Bridge.wordOfString y))

  have hind :
      FiniteDependence.MIS.Model.prob μ (cylStr (a := (0 : ℤ)) x ∩ cylStr (a := (m + 5 : ℤ)) y) =
        FiniteDependence.MIS.Model.prob μ (cylStr (a := (0 : ℤ)) x) *
          FiniteDependence.MIS.Model.prob μ (cylStr (a := (m + 5 : ℤ)) y) := by
    simpa [hxLen] using hind0

  -- Stationarity shifts the `y`-cylinder from `m+5` back to 0.
  have hshift :
      FiniteDependence.MIS.Model.prob μ (cylStr (a := (m + 5 : ℤ)) y) =
        FiniteDependence.MIS.Model.prob μ (cylStr (a := (0 : ℤ)) y) := by
    simpa using
      (Stationary.prob_cylStr_add_nat (μ := μ) hstat (a := (0 : ℤ)) (n := m + 5) (s := y))

  let L : Nat := m + 5 + n
  let S : Finset String :=
    (allowedWordsFinset L).filter (fun w => prefixOf w m = x ∧ suffixFrom w (m + 5) = y)

  have hset :
      cylStr (a := (0 : ℤ)) x ∩ cylStr (a := (m + 5 : ℤ)) y =
        ⋃ w ∈ S, cylStr (a := (0 : ℤ)) w := by
    ext ω
    constructor
    · rintro ⟨hxω, hyω⟩
      -- Choose `w := blockString 0 L ω`.
      let w : String := blockString (a := (0 : ℤ)) L ω
      have hw_allowed : w ∈ K5Data.allowedWords L := by
        simpa [w, L, Nat.add_left_comm, Nat.add_comm] using
          (blockString_mem_allowedWords (ω := ω) (a := (0 : ℤ)) (n := m + 4 + n))
      have hw_fin : w ∈ allowedWordsFinset L :=
        (mem_allowedWordsFinset_iff (L := L) (s := w)).2 hw_allowed
      have hw01 : Is01String w := Is01String.of_mem_allowedWords (L := L) (s := w) hw_allowed

      have hxBlock : blockString (a := (0 : ℤ)) m ω = x := by
        have := (mem_cylStr_iff_blockString_eq (a := (0 : ℤ)) x ω hx01).1 hxω
        simpa [hxLen] using this
      have hyBlock : blockString (a := (m + 5 : ℤ)) n ω = y := by
        have := (mem_cylStr_iff_blockString_eq (a := (m + 5 : ℤ)) y ω hy01).1 hyω
        simpa [hyLen] using this

      have hmL : m ≤ L := by
        simpa [L, Nat.add_assoc] using (Nat.le_add_right m (5 + n))

      have hw_pref : prefixOf w m = x := by
        have := prefixOf_blockString (ω := ω) (a := (0 : ℤ)) (L := L) (m := m) hmL
        simpa [w, hxBlock] using this

      have hw_suf : suffixFrom w (m + 5) = y := by
        have hdrop :
            String.ofList ((blockString (a := (0 : ℤ)) L ω).toList.drop (m + 5)) =
              blockString (a := (0 : ℤ) + (m + 5)) n ω := by
          simpa [L] using
            (ofList_drop_blockString_add (ω := ω) (a := (0 : ℤ)) (m := m + 5) (n := n))
        have hdrop' :
            suffixFrom w (m + 5) = blockString (a := (m + 5 : ℤ)) n ω := by
          simpa [suffixFrom, w, L, add_assoc, add_left_comm, add_comm] using hdrop
        simpa [hdrop', hyBlock]

      have hwS : w ∈ S := by
        exact Finset.mem_filter.2 ⟨hw_fin, ⟨hw_pref, hw_suf⟩⟩

      have hmem : ω ∈ cylStr (a := (0 : ℤ)) w := by
        have hwLen : w.length = L := by
          simpa [w] using (blockString_length (a := (0 : ℤ)) (n := L) (ω := ω))
        have : blockString (a := (0 : ℤ)) w.length ω = w := by
          simpa [hwLen, w]
        exact (mem_cylStr_iff_blockString_eq (a := (0 : ℤ)) w ω hw01).2 this

      exact mem_iUnion.2 ⟨w, mem_iUnion.2 ⟨hwS, hmem⟩⟩
    · intro hω
      rcases mem_iUnion.1 hω with ⟨w, hwω⟩
      rcases mem_iUnion.1 hwω with ⟨hwS, hwMem⟩
      have hw_fin : w ∈ allowedWordsFinset L := (Finset.mem_filter.1 hwS).1
      have hw_pred : prefixOf w m = x ∧ suffixFrom w (m + 5) = y := (Finset.mem_filter.1 hwS).2
      have hw_allowed : w ∈ K5Data.allowedWords L :=
        (mem_allowedWordsFinset_iff (L := L) (s := w)).1 hw_fin
      have hw01 : Is01String w := Is01String.of_mem_allowedWords (L := L) (s := w) hw_allowed
      have hwLen : w.length = L := length_of_mem_allowedWords (L := L) (s := w) hw_allowed

      have hblockFull : blockString (a := (0 : ℤ)) L ω = w := by
        have := (mem_cylStr_iff_blockString_eq (a := (0 : ℤ)) w ω hw01).1 hwMem
        simpa [hwLen] using this

      have hmL : m ≤ L := by
        simpa [L, Nat.add_assoc] using (Nat.le_add_right m (5 + n))

      have hxBlock : blockString (a := (0 : ℤ)) m ω = x := by
        have := prefixOf_blockString (ω := ω) (a := (0 : ℤ)) (L := L) (m := m) hmL
        have : blockString (a := (0 : ℤ)) m ω = prefixOf w m := by
          simpa [hblockFull] using this.symm
        simpa [this, hw_pred.1]

      have hyBlock : blockString (a := (m + 5 : ℤ)) n ω = y := by
        have hdrop :
            String.ofList ((blockString (a := (0 : ℤ)) L ω).toList.drop (m + 5)) =
              blockString (a := (0 : ℤ) + (m + 5)) n ω := by
          simpa [L] using
            (ofList_drop_blockString_add (ω := ω) (a := (0 : ℤ)) (m := m + 5) (n := n))
        have hdrop' : blockString (a := (m + 5 : ℤ)) n ω = String.ofList (w.toList.drop (m + 5)) := by
          -- Rewrite the full block `blockString 0 L ω` to `w`.
          simpa [hblockFull] using hdrop.symm
        have : blockString (a := (m + 5 : ℤ)) n ω = suffixFrom w (m + 5) := by
          simpa [suffixFrom] using hdrop'
        simpa [this, hw_pred.2]

      have hxω : ω ∈ cylStr (a := (0 : ℤ)) x :=
        (mem_cylStr_iff_blockString_eq (a := (0 : ℤ)) x ω hx01).2 (by simpa [hxLen] using hxBlock)
      have hyω : ω ∈ cylStr (a := (m + 5 : ℤ)) y :=
        (mem_cylStr_iff_blockString_eq (a := (m + 5 : ℤ)) y ω hy01).2 (by simpa [hyLen] using hyBlock)
      exact ⟨hxω, hyω⟩

  have hd : PairwiseDisjoint (↑S : Set String) (fun w => cylStr (a := (0 : ℤ)) w) := by
    intro w hw u hu hwu
    have hw0 : w ∈ allowedWordsFinset L := (Finset.mem_filter.1 hw).1
    have hu0 : u ∈ allowedWordsFinset L := (Finset.mem_filter.1 hu).1
    exact pairwiseDisjoint_cylStr_allowedWords (a := (0 : ℤ)) (L := L) hw0 hu0 hwu

  have hmS : ∀ w ∈ S, MeasurableSet (cylStr (a := (0 : ℤ)) w) := by
    intro w _hw
    simpa using measurableSet_cylStr (a := (0 : ℤ)) (s := w)

  have hprobUnion :
      FiniteDependence.MIS.Model.prob μ (⋃ w ∈ S, cylStr (a := (0 : ℤ)) w) =
        ∑ w ∈ S, FiniteDependence.MIS.Model.prob μ (cylStr (a := (0 : ℤ)) w) :=
    prob_biUnion_finset (μ := μ) (s := S) (f := fun w => cylStr (a := (0 : ℤ)) w) hd hmS

  have hsum :
      FiniteDependence.MIS.Model.prob μ (cylStr (a := (0 : ℤ)) x ∩ cylStr (a := (m + 5 : ℤ)) y) =
        ∑ w ∈ S, FiniteDependence.MIS.Model.prob μ (cylStr (a := (0 : ℤ)) w) := by
    simpa [hset] using hprobUnion

  -- Put everything together.
  calc
    FiniteDependence.MIS.Model.prob μ (cylStr (a := (0 : ℤ)) x) *
        FiniteDependence.MIS.Model.prob μ (cylStr (a := (0 : ℤ)) y) =
        FiniteDependence.MIS.Model.prob μ (cylStr (a := (0 : ℤ)) x) *
          FiniteDependence.MIS.Model.prob μ (cylStr (a := (m + 5 : ℤ)) y) := by
          simp [hshift]
    _ = FiniteDependence.MIS.Model.prob μ (cylStr (a := (0 : ℤ)) x ∩ cylStr (a := (m + 5 : ℤ)) y) := by
          simpa using hind.symm
    _ = ∑ w ∈ S, FiniteDependence.MIS.Model.prob μ (cylStr (a := (0 : ℤ)) w) := hsum
    _ = ∑ w ∈ (allowedWordsFinset (m + 5 + n)).filter (fun w => prefixOf w m = x ∧ suffixFrom w (m + 5) = y),
          FiniteDependence.MIS.Model.prob μ (cylStr (a := (0 : ℤ)) w) := by
          rfl

end

end Model

end K5Bridge

end FiniteDependence.MIS
