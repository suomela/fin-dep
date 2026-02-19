import FiniteDependence.MIS.K5Bridge.Partition
import FiniteDependence.MIS.Prob

namespace FiniteDependence.MIS

/-!
Prefix probabilities as finite sums over length-`L` cylinder probabilities.

This is the measure-theoretic statement used by the `k=5` bridge:
probabilities of shorter cylinders are sums of probabilities of longer cylinders
with the corresponding prefix.
-/

namespace K5Bridge

open K5Data

open MeasureTheory Set

open scoped BigOperators

namespace Model

open FiniteDependence.MIS.Model

noncomputable section

/-- The length-`m` prefix of a string, implemented via `toList.take`. -/
def prefixOf (s : String) (m : Nat) : String :=
  String.ofList (s.toList.take m)

/-- Drop the first character of a string (used for one-step suffix stationarity). -/
def suffix1 (s : String) : String :=
  String.ofList (s.toList.drop 1)

lemma prefixOf_toList (s : String) (m : Nat) : (prefixOf s m).toList = s.toList.take m := by
  simp [prefixOf]

lemma suffix1_toList (s : String) : (suffix1 s).toList = s.toList.drop 1 := by
  simp [suffix1]

lemma Is01String.prefixOf {s : String} (hs : Is01String s) (m : Nat) : Is01String (prefixOf s m) := by
  intro c hc
  have hc' : c ∈ s.toList := by
    -- `prefixOf` only drops characters, so membership implies membership in the original list.
    have : c ∈ s.toList.take m := by simpa [prefixOf_toList] using hc
    exact List.mem_of_mem_take this
  exact hs c hc'

lemma toList_take_blockString (ω : FiniteDependence.MIS.State) (a : ℤ) :
    ∀ {L m : Nat}, m ≤ L →
      (blockString a L ω).toList.take m = (blockString a m ω).toList := by
  intro L m hm
  induction L generalizing m with
  | zero =>
      have hm0 : m = 0 := Nat.eq_zero_of_le_zero hm
      subst hm0
      simp [blockString]
  | succ L ih =>
      cases m with
      | zero =>
          simp [blockString]
      | succ m =>
          have hmL : m ≤ L := Nat.le_of_succ_le_succ hm
          -- Split into `m < L` (prefix is inside the old part) vs `m = L` (take the whole list).
          cases (Nat.lt_or_eq_of_le hmL) with
          | inl hlt =>
              have hm' : Nat.succ m ≤ L := Nat.succ_le_of_lt hlt
              have hlen :
                  (blockString a L ω).toList.length = L := by
                simpa [String.length_toList] using
                  (blockString_length (a := a) (n := L) (ω := ω))
              have hm'' : Nat.succ m ≤ (blockString a L ω).toList.length := by
                simpa [hlen] using hm'
              -- `blockString (L+1)` is `blockString L` with one extra character at the end.
              calc
                (blockString a (L + 1) ω).toList.take (m + 1) =
                    ((blockString a L ω).toList ++
                      [if ω.1 (a + Int.ofNat L) then '1' else '0']).take (m + 1) := by
                      simp [blockString, String.toList_push, Nat.add_comm, Nat.add_left_comm, Nat.add_assoc]
                _ = (blockString a L ω).toList.take (m + 1) := by
                      simpa [List.take_append_of_le_length hm'']
                _ = (blockString a (m + 1) ω).toList := by
                      simpa [Nat.succ_eq_add_one] using ih (m := m + 1) hm'
          | inr hEq =>
              -- Fix `m = L`, keeping `L` (not eliminating it).
              subst m
              have hlen :
                  (blockString a (L + 1) ω).toList.length = L + 1 := by
                simpa [String.length_toList] using
                  (blockString_length (a := a) (n := L + 1) (ω := ω))
              calc
                (blockString a (L + 1) ω).toList.take (L + 1) =
                    (blockString a (L + 1) ω).toList.take (blockString a (L + 1) ω).toList.length := by
                      simpa [hlen]
                _ = (blockString a (L + 1) ω).toList := by
                      simpa using (List.take_length (l := (blockString a (L + 1) ω).toList))
                _ = (blockString a (L + 1) ω).toList := rfl

lemma prefixOf_blockString (ω : FiniteDependence.MIS.State) (a : ℤ) {L m : Nat} (hm : m ≤ L) :
    prefixOf (blockString a L ω) m = blockString a m ω := by
  apply String.ext
  -- Compare `toList`s.
  have ht : (blockString a L ω).toList.take m = (blockString a m ω).toList :=
    toList_take_blockString (ω := ω) (a := a) (L := L) (m := m) hm
  simpa [prefixOf_toList] using ht

lemma toList_blockString_add (ω : FiniteDependence.MIS.State) (a : ℤ) (m n : Nat) :
    (blockString a (m + n) ω).toList =
      (blockString a m ω).toList ++ (blockString (a + m) n ω).toList := by
  induction n with
  | zero =>
      simp [blockString]
  | succ n ih =>
      -- `blockString` extends by pushing the next character.
      -- Use the induction hypothesis, then reassociate the concatenations.
      simp [blockString, ih, Nat.add_assoc, String.toList_push, List.append_assoc, Nat.cast_add,
        add_assoc, add_left_comm, add_comm]

lemma toList_drop_blockString_add (ω : FiniteDependence.MIS.State) (a : ℤ) (m n : Nat) :
    (blockString a (m + n) ω).toList.drop m = (blockString (a + m) n ω).toList := by
  have happ := toList_blockString_add (ω := ω) (a := a) (m := m) (n := n)
  have hlen' : (blockString a m ω).toList.length = m := by
    simpa [String.length_toList] using (blockString_length (a := a) (n := m) (ω := ω))
  have hlen : m ≤ (blockString a m ω).toList.length := by
    simpa [hlen'] using (le_rfl : m ≤ m)
  calc
    (blockString a (m + n) ω).toList.drop m =
        ((blockString a m ω).toList ++ (blockString (a + m) n ω).toList).drop m := by
          simpa [happ]
    _ = (blockString a m ω).toList.drop m ++ (blockString (a + m) n ω).toList := by
          simpa using
            (List.drop_append_of_le_length (l₁ := (blockString a m ω).toList)
              (l₂ := (blockString (a + m) n ω).toList) (i := m) hlen)
    _ = (blockString (a + m) n ω).toList := by
          have hdrop : (blockString a m ω).toList.drop m = [] := by
            apply List.drop_eq_nil_of_le
            simpa [hlen'] using (le_rfl : m ≤ m)
          simpa [hdrop]

lemma ofList_drop_blockString_add (ω : FiniteDependence.MIS.State) (a : ℤ) (m n : Nat) :
    String.ofList ((blockString a (m + n) ω).toList.drop m) = blockString (a + m) n ω := by
  apply String.ext
  simp [toList_drop_blockString_add, String.toList_ofList]

lemma prob_biUnion_finset {μ : Measure FiniteDependence.MIS.State} [IsProbabilityMeasure μ]
    {s : Finset String} {f : String → Set FiniteDependence.MIS.State}
    (hd : PairwiseDisjoint (↑s : Set String) f) (hm : ∀ b ∈ s, MeasurableSet (f b)) :
    FiniteDependence.MIS.Model.prob μ (⋃ b ∈ s, f b) = ∑ b ∈ s, FiniteDependence.MIS.Model.prob μ (f b) := by
  have hμ : μ (⋃ b ∈ s, f b) = ∑ b ∈ s, μ (f b) :=
    MeasureTheory.measure_biUnion_finset (μ := μ) hd hm
  have h' := congrArg ENNReal.toReal hμ
  have htop : ∀ b ∈ s, μ (f b) ≠ (⊤ : ENNReal) := by
    intro b hb
    exact measure_ne_top μ (f b)
  -- Convert to reals (`prob`) and pull `toReal` through the finite sum.
  simpa [FiniteDependence.MIS.Model.prob, ENNReal.toReal_sum htop] using h'

lemma prob_prefix_eq_sum {μ : Measure FiniteDependence.MIS.State} [IsProbabilityMeasure μ]
    (a : ℤ) {L m : Nat} (hL : 0 < L) (hm : m ≤ L) {x : String}
    (hx01 : Is01String x) (hxLen : x.length = m) :
    FiniteDependence.MIS.Model.prob μ (cylStr (a := a) x) =
      ∑ w ∈ (allowedWordsFinset L).filter (fun w => prefixOf w m = x),
        FiniteDependence.MIS.Model.prob μ (cylStr (a := a) w) := by
  classical
  -- Set of length-`L` words with prefix `x`.
  let S : Finset String := (allowedWordsFinset L).filter (fun w => prefixOf w m = x)

  -- First show a set equality: the `m`-cylinder equals a union of `L`-cylinders with prefix `x`.
  have hset :
      cylStr (a := a) x = ⋃ w ∈ S, cylStr (a := a) w := by
    ext ω
    constructor
    · intro hx
      -- Choose `w := blockString a L ω`.
      cases L with
      | zero =>
          cases (Nat.lt_asymm hL hL)
      | succ n =>
          let w : String := blockString a (n + 1) ω
          have hw_allowed : w ∈ K5Data.allowedWords (n + 1) := by
            simpa [w] using
              (K5Bridge.Model.blockString_mem_allowedWords (ω := ω) (a := a) (n := n))
          have hw_fin : w ∈ allowedWordsFinset (n + 1) :=
            (mem_allowedWordsFinset_iff (L := n + 1) (s := w)).2 hw_allowed
          have hw01 : Is01String w := Is01String.of_mem_allowedWords (L := n + 1) (s := w) hw_allowed
          have hwLen : w.length = n + 1 := by
            simpa [w] using (K5Bridge.Model.blockString_length (a := a) (n := n + 1) (ω := ω))
          -- `ω ∈ cylStr w` (tautologically).
          have hωw : ω ∈ cylStr (a := a) w := by
            have : blockString a w.length ω = w := by
              simpa [w, hwLen]
            exact (mem_cylStr_iff_blockString_eq (a := a) w ω hw01).2 this

          -- `w` has prefix `x` because `blockString a m ω = x`.
          have hx_block : blockString a m ω = x := by
            -- rewrite the `cylStr` membership as a `blockString` equality
            have := (mem_cylStr_iff_blockString_eq (a := a) x ω hx01).1 hx
            simpa [hxLen] using this
          have hw_pref : prefixOf w m = x := by
            -- `prefixOf w m = blockString a m ω` for `w = blockString a (n+1) ω`.
            have hw' : prefixOf (blockString a (n + 1) ω) m = blockString a m ω :=
              prefixOf_blockString (ω := ω) (a := a) (L := n + 1) (m := m) (by
                -- `m ≤ n+1` from `m ≤ L` and `L = n+1`
                simpa using hm)
            simpa [w, hw', hx_block]

          have hwS : w ∈ S := by
            -- membership in the filtered finset
            have : w ∈ allowedWordsFinset (n + 1) ∧ prefixOf w m = x := by
              exact ⟨hw_fin, hw_pref⟩
            simpa [S, Finset.mem_filter] using this

          -- conclude membership in the union
          refine mem_iUnion.2 ⟨w, ?_⟩
          refine mem_iUnion.2 ⟨hwS, ?_⟩
          exact hωw
    · intro hω
      -- Union-of-length-`L` cylinders implies the `m`-prefix cylinder.
      rcases mem_iUnion.1 hω with ⟨w, hw⟩
      rcases mem_iUnion.1 hw with ⟨hwS, hωw⟩
      have hw_fin : w ∈ allowedWordsFinset L := by
        -- `w ∈ S` implies `w ∈ allowedWordsFinset L`
        exact (Finset.mem_of_mem_filter w hwS)
      have hw_allowed : w ∈ K5Data.allowedWords L :=
        (mem_allowedWordsFinset_iff (L := L) (s := w)).1 hw_fin
      have hw01 : Is01String w := Is01String.of_mem_allowedWords (L := L) (s := w) hw_allowed
      have hwLen : w.length = L := length_of_mem_allowedWords (L := L) (s := w) hw_allowed

      have hw_pref : prefixOf w m = x := by
        -- membership in the filter gives the prefix condition
        have hwS' : w ∈ allowedWordsFinset L ∧ prefixOf w m = x := by
          simpa [S, Finset.mem_filter] using hwS
        exact hwS'.2

      -- From `ω ∈ cylStr w`, get `blockString a m ω = prefixOf w m = x`.
      have hw_block : blockString a L ω = w := by
        have := (mem_cylStr_iff_blockString_eq (a := a) w ω hw01).1 hωw
        simpa [hwLen] using this

      have hx_block : blockString a m ω = x := by
        have : prefixOf (blockString a L ω) m = blockString a m ω :=
          prefixOf_blockString (ω := ω) (a := a) (L := L) (m := m) hm
        -- rewrite `blockString a L ω` to `w` and use the prefix condition.
        simpa [hw_block, hw_pref] using this.symm

      -- Convert back to cylinder membership.
      have : ω ∈ cylStr (a := a) x := by
        have : blockString a x.length ω = x := by simpa [hxLen] using hx_block
        exact (mem_cylStr_iff_blockString_eq (a := a) x ω hx01).2 this
      exact this

  -- Now take probabilities and sum over the disjoint union.
  have hdS : PairwiseDisjoint (↑S : Set String) (fun w => cylStr (a := a) w) := by
    -- inherited from the full `allowedWordsFinset L` disjointness
    intro w hw u hu hwu
    have hw0 : w ∈ allowedWordsFinset L := Finset.mem_of_mem_filter w hw
    have hu0 : u ∈ allowedWordsFinset L := Finset.mem_of_mem_filter u hu
    exact pairwiseDisjoint_cylStr_allowedWords (a := a) (L := L) hw0 hu0 hwu

  have hmS : ∀ w ∈ S, MeasurableSet (cylStr (a := a) w) := by
    intro w _hw
    simpa using measurableSet_cylStr (a := a) (s := w)

  -- Use the finite-disjoint-union formula for `prob`.
  have hprobUnion :
      FiniteDependence.MIS.Model.prob μ (⋃ w ∈ S, cylStr (a := a) w) =
        ∑ w ∈ S, FiniteDependence.MIS.Model.prob μ (cylStr (a := a) w) :=
    prob_biUnion_finset (μ := μ) (s := S) (f := fun w => cylStr (a := a) w) hdS hmS

  -- Rewrite the LHS using the set equality `hset`, then unfold `S`.
  have hprob :
      FiniteDependence.MIS.Model.prob μ (cylStr (a := a) x) =
        ∑ w ∈ S, FiniteDependence.MIS.Model.prob μ (cylStr (a := a) w) := by
    simpa [hset.symm] using hprobUnion
  simpa [S] using hprob

lemma prob_suffix1_eq_sum {μ : Measure FiniteDependence.MIS.State} [IsProbabilityMeasure μ]
    (a : ℤ) {m : Nat} {x : String} (hx01 : Is01String x) (hxLen : x.length = m) :
    FiniteDependence.MIS.Model.prob μ (cylStr (a := a + 1) x) =
      ∑ w ∈ (allowedWordsFinset (m + 1)).filter (fun w => suffix1 w = x),
        FiniteDependence.MIS.Model.prob μ (cylStr (a := a) w) := by
  classical
  let L : Nat := m + 1
  let S : Finset String := (allowedWordsFinset L).filter (fun w => suffix1 w = x)

  have hsuf_block (ω : FiniteDependence.MIS.State) :
      suffix1 (blockString a L ω) = blockString (a + 1) m ω := by
    -- `drop 1` from a length-`m+1` block is the length-`m` block starting at `a+1`.
    -- This is exactly `ofList_drop_blockString_add` with `(m,n) = (1,m)`.
    simpa [L, suffix1, Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using
      (ofList_drop_blockString_add (ω := ω) (a := a) (m := 1) (n := m))

  have hset : cylStr (a := a + 1) x = ⋃ w ∈ S, cylStr (a := a) w := by
    ext ω
    constructor
    · intro hxω
      -- Choose `w := blockString a (m+1) ω`.
      let w : String := blockString a L ω
      have hw_allowed : w ∈ K5Data.allowedWords L := by
        -- `blockString_mem_allowedWords` is stated for `n+1`.
        simpa [L, w] using (K5Bridge.Model.blockString_mem_allowedWords (ω := ω) (a := a) (n := m))
      have hw_fin : w ∈ allowedWordsFinset L :=
        (mem_allowedWordsFinset_iff (L := L) (s := w)).2 hw_allowed
      have hw01 : Is01String w := Is01String.of_mem_allowedWords (L := L) (s := w) hw_allowed
      have hwLen : w.length = L := by
        simpa [w] using (K5Bridge.Model.blockString_length (a := a) (n := L) (ω := ω))
      have hωw : ω ∈ cylStr (a := a) w := by
        have : blockString a w.length ω = w := by
          simpa [w, hwLen]
        exact (mem_cylStr_iff_blockString_eq (a := a) w ω hw01).2 this
      have hx_block : blockString (a + 1) m ω = x := by
        have := (mem_cylStr_iff_blockString_eq (a := a + 1) x ω hx01).1 hxω
        simpa [hxLen] using this
      have hw_suf : suffix1 w = x := by
        simpa [w, hsuf_block, hx_block]
      have hwS : w ∈ S := by
        have : w ∈ allowedWordsFinset L ∧ suffix1 w = x := by
          exact ⟨hw_fin, hw_suf⟩
        simpa [S, Finset.mem_filter] using this
      exact mem_iUnion.2 ⟨w, mem_iUnion.2 ⟨hwS, hωw⟩⟩
    · intro hω
      rcases mem_iUnion.1 hω with ⟨w, hw⟩
      rcases mem_iUnion.1 hw with ⟨hwS, hωw⟩
      have hw_fin : w ∈ allowedWordsFinset L := Finset.mem_of_mem_filter w hwS
      have hw_allowed : w ∈ K5Data.allowedWords L := (mem_allowedWordsFinset_iff (L := L) (s := w)).1 hw_fin
      have hw01 : Is01String w := Is01String.of_mem_allowedWords (L := L) (s := w) hw_allowed
      have hwLen : w.length = L := length_of_mem_allowedWords (L := L) (s := w) hw_allowed
      have hw_suf : suffix1 w = x := (Finset.mem_filter.1 hwS).2
      have hw_block : blockString a L ω = w := by
        have := (mem_cylStr_iff_blockString_eq (a := a) w ω hw01).1 hωw
        simpa [hwLen] using this
      have hx_block : blockString (a + 1) m ω = x := by
        have : suffix1 (blockString a L ω) = x := by simpa [hw_block] using hw_suf
        simpa [hsuf_block] using this
      have : ω ∈ cylStr (a := a + 1) x := by
        have : blockString (a + 1) x.length ω = x := by simpa [hxLen] using hx_block
        exact (mem_cylStr_iff_blockString_eq (a := a + 1) x ω hx01).2 this
      exact this

  have hdS : PairwiseDisjoint (↑S : Set String) (fun w => cylStr (a := a) w) := by
    intro w hw u hu hwu
    have hw0 : w ∈ allowedWordsFinset L := Finset.mem_of_mem_filter w hw
    have hu0 : u ∈ allowedWordsFinset L := Finset.mem_of_mem_filter u hu
    exact pairwiseDisjoint_cylStr_allowedWords (a := a) (L := L) hw0 hu0 hwu

  have hmS : ∀ w ∈ S, MeasurableSet (cylStr (a := a) w) := by
    intro w _hw
    simpa using measurableSet_cylStr (a := a) (s := w)

  have hprobUnion :
      FiniteDependence.MIS.Model.prob μ (⋃ w ∈ S, cylStr (a := a) w) =
        ∑ w ∈ S, FiniteDependence.MIS.Model.prob μ (cylStr (a := a) w) :=
    prob_biUnion_finset (μ := μ) (s := S) (f := fun w => cylStr (a := a) w) hdS hmS

  have hprob :
      FiniteDependence.MIS.Model.prob μ (cylStr (a := a + 1) x) =
        ∑ w ∈ S, FiniteDependence.MIS.Model.prob μ (cylStr (a := a) w) := by
    simpa [hset.symm] using hprobUnion
  simpa [S, L] using hprob

end

end Model

end K5Bridge

end FiniteDependence.MIS
