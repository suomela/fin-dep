import FiniteDependence.Coloring.ColoringProcess

import Mathlib.Data.Finset.Sort
import Mathlib.Data.List.Chain
import Mathlib.Data.List.Flatten
import Mathlib.Data.List.TakeDrop
import Mathlib.Data.List.TakeWhile
import Mathlib.Tactic

/-!
# Contiguous vs noncontiguous finite dependence

This file formalizes the "noncontiguous" (`IndexSeparated`) notion of `k`-dependence for
processes on `ℤ` and proves it is equivalent to the Holroyd–Liggett "cut" definition used in this
repository (`IsKDependent`).
-/

open scoped BigOperators

namespace FiniteDependence.Coloring

open MeasureTheory ProbabilityTheory

namespace DependenceEquivalence

/-! ## Basic lattice lemmas for coordinate σ-algebras -/

variable {q : ℕ}

lemma coordMeasurableSpace_mono {A B : Set ℤ} (hAB : A ⊆ B) :
    coordMeasurableSpace (q := q) A ≤ coordMeasurableSpace (q := q) B := by
  classical
  refine iSup_le ?_
  rintro ⟨j, hjA⟩
  have hjB : j ∈ B := hAB hjA
  exact le_iSup (fun j : {j : ℤ // j ∈ B} =>
    MeasurableSpace.comap (fun x : ℤ → Fin q => x j.1) inferInstance) ⟨j, hjB⟩

lemma coordMeasurableSpace_le_pi (A : Set ℤ) :
    coordMeasurableSpace (q := q) A ≤ (MeasurableSpace.pi : MeasurableSpace (ℤ → Fin q)) := by
  classical
  refine iSup_le ?_
  intro j
  have hmeas : Measurable (fun x : ℤ → Fin q => x j.1) := by
    simpa using (measurable_pi_apply (a := j.1))
  exact hmeas.comap_le

lemma coordMeasurableSpace_past_eq (i : ℤ) :
    pastMeasurableSpace (q := q) i = coordMeasurableSpace (q := q) {j : ℤ | j < i} := rfl

lemma coordMeasurableSpace_future_eq (i : ℤ) (k : ℕ) :
    futureMeasurableSpace (q := q) i k = coordMeasurableSpace (q := q) {j : ℤ | i + k ≤ j} := rfl

/-! ## The easy direction: noncontiguous ⇒ cut -/

theorem isKDependent_of_isKDependentNoncontig {μ : ProbabilityMeasure (ℤ → Fin q)} {k : ℕ}
    (h : IsKDependentNoncontig (q := q) μ k) : IsKDependent (q := q) μ k := by
  intro i
  -- Apply noncontiguous dependence to the two half-lines.
  have hsep : IndexSeparated ({j : ℤ | j < i}) ({j : ℤ | i + k ≤ j}) k := by
    intro a ha b hb
    -- Here `a < i ≤ b - k`, so `b - a ≥ k+1`.
    have hab : a < b := lt_of_lt_of_le ha (le_trans (by linarith) hb)
    -- Convert the separation into a statement on `natAbs`.
    have : (k : ℤ) < b - a := by
      have : (i + k : ℤ) - a ≤ b - a := sub_le_sub_right hb a
      have : (k : ℤ) + (i - a) ≤ b - a := by
        -- `(i+k) - a = (i-a) + k`
        simpa [sub_eq_add_neg, add_assoc, add_left_comm, add_comm] using this
      -- Since `a < i`, we have `0 < i - a`.
      have hpos : 0 < i - a := sub_pos.2 ha
      -- So `k < k + (i-a) ≤ b-a`.
      have hklt : (k : ℤ) < (k : ℤ) + (i - a) := lt_add_of_pos_right _ hpos
      exact lt_of_lt_of_le hklt (by linarith)
    -- Since `a < b`, `|a-b| = b-a`.
    have habs : (Int.natAbs (a - b) : ℤ) = b - a := by
      have hneg : a - b < 0 := sub_neg.2 hab
      calc
        (Int.natAbs (a - b) : ℤ) = |a - b| := by
          exact Int.natCast_natAbs (a - b)
        _ = -(a - b) := by simpa using (abs_of_neg hneg)
        _ = b - a := by abel
    -- Cast the strict inequality to `Nat` and finish.
    have : (k : ℤ) < (Int.natAbs (a - b) : ℤ) := by simpa [habs] using this
    exact_mod_cast this
  simpa [coordMeasurableSpace_past_eq (q := q), coordMeasurableSpace_future_eq (q := q)] using
    h (A := {j : ℤ | j < i}) (B := {j : ℤ | i + k ≤ j}) hsep

/-! ## List-based decomposition into alternating chunks -/

private def groupBySide (side : ℤ → Bool) : List ℤ → List (Bool × List ℤ)
  | [] => []
  | x :: xs =>
      let b := side x
      match groupBySide side xs with
      | [] => [(b, [x])]
      | (b', ys) :: rest =>
          if b = b' then
            (b', x :: ys) :: rest
          else
            (b, [x]) :: (b', ys) :: rest

private lemma groupBySide_eq_nil_iff (side : ℤ → Bool) (l : List ℤ) :
    groupBySide side l = [] ↔ l = [] := by
  cases l with
  | nil =>
      simp [groupBySide]
  | cons x xs =>
      constructor
      · intro h
        have : False := by
          cases hxs : groupBySide side xs with
          | nil =>
              -- then `groupBySide side (x :: xs) = [(side x, [x])]`
              simp [groupBySide, hxs] at h
          | cons g gs =>
              -- regardless of the `if`, the result is nonempty
              by_cases hb : side x = g.1
              · simp [groupBySide, hxs, hb] at h
              · simp [groupBySide, hxs, hb] at h
        exact (False.elim this)
      · intro h
        cases h

private lemma bind_groupBySide_eq (side : ℤ → Bool) (l : List ℤ) :
    (groupBySide side l).flatMap (fun g => g.2) = l := by
  classical
  induction l with
  | nil =>
      simp [groupBySide]
  | cons x xs ih =>
      -- Unfold one step and split on whether we merge `x` into the first chunk of `xs`.
      cases h : groupBySide side xs with
      | nil =>
          have : xs = [] := (groupBySide_eq_nil_iff side xs).1 h
          subst this
          simp [groupBySide]
      | cons g gs =>
          rcases g with ⟨b', ys⟩
          by_cases hb : side x = b'
          · -- Use the inductive hypothesis, rewritten using `h`.
            have ih' : ys ++ List.flatMap (fun g => g.2) gs = xs := by
              simpa [h] using ih
            simp [groupBySide, h, hb, ih']
          · have ih' : ys ++ List.flatMap (fun g => g.2) gs = xs := by
              simpa [h] using ih
            simp [groupBySide, h, hb, ih']

/-! ## Building `iIndep` from successive independence -/

section iIndep

variable {Ω : Type*} {_mΩ : MeasurableSpace Ω} {μ : Measure Ω}
variable {ι : Type*} [LinearOrder ι] [DecidableEq ι]
variable {m : ι → MeasurableSpace Ω}

theorem iIndep_of_indep_iSup_lt [IsProbabilityMeasure μ]
    (hind : ∀ a : ι, Indep (m a) (⨆ b : {b : ι // b < a}, m b.1) μ) :
    iIndep m μ := by
  classical
  -- Unfold `iIndep` into the finite-intersection factorization.
  rw [ProbabilityTheory.iIndep_iff]
  intro s f hf
  -- Induct on `s` by inserting a new maximum each time.
  have hs_all :
      (∀ i ∈ s, MeasurableSet[m i] (f i)) → μ (⋂ i ∈ s, f i) = ∏ i ∈ s, μ (f i) := by
    refine Finset.induction_on_max s (p := fun s =>
        (∀ i ∈ s, MeasurableSet[m i] (f i)) → μ (⋂ i ∈ s, f i) = ∏ i ∈ s, μ (f i)) ?_ ?_
    · intro _
      simp
    · intro a s ha_gt hs hf'
      -- Apply the inductive hypothesis to the smaller finset.
      have hs' : μ (⋂ i ∈ s, f i) = ∏ i ∈ s, μ (f i) := by
        refine hs ?_
        intro i hi
        exact hf' i (by simp [hi])
      -- The σ-algebra generated by the previously inserted indices.
      let mPrev : MeasurableSpace Ω := ⨆ i ∈ s, m i
      have h_mPrev_le :
          mPrev ≤ (⨆ b : {b : ι // b < a}, m b.1) := by
        refine iSup₂_le ?_
        intro i hi
        have hlt : i < a := ha_gt i hi
        exact le_iSup (fun b : {b : ι // b < a} => m b.1) ⟨i, hlt⟩
      have hind' : Indep (m a) mPrev μ :=
        ProbabilityTheory.indep_of_indep_of_le_right (hind a) h_mPrev_le
      -- The intersection over `s` is measurable in `mPrev`.
      have hmeasPrev : MeasurableSet[mPrev] (⋂ i ∈ s, f i) := by
        have h_each : ∀ i ∈ s, MeasurableSet[mPrev] (f i) := by
          intro i hi
          have hmi : m i ≤ mPrev := by
            refine le_trans (le_iSup (fun _ : i ∈ s => m i) hi) ?_
            simpa [mPrev] using (le_iSup (fun j : ι => ⨆ (_ : j ∈ s), m j) i)
          exact hmi (f i) (hf' i (by simp [hi]))
        simpa using s.measurableSet_biInter h_each
      have hmeasA : MeasurableSet[m a] (f a) := by
        simpa using hf' a (by simp)
      -- Use independence to factor the new intersection.
      have hIndepSet : IndepSet (f a) (⋂ i ∈ s, f i) μ :=
        ProbabilityTheory.Indep.indepSet_of_measurableSet hind' hmeasA hmeasPrev
      have ha_notin : a ∉ s := by
        intro ha_mem
        exact lt_irrefl a (ha_gt a ha_mem)
      -- Finish by rewriting the intersection and product over `insert a s`.
      calc
        μ (⋂ i ∈ insert a s, f i) = μ (f a ∩ ⋂ i ∈ s, f i) := by
          simp
        _ = μ (f a) * μ (⋂ i ∈ s, f i) := by
          simpa using hIndepSet.measure_inter_eq_mul
        _ = μ (f a) * ∏ i ∈ s, μ (f i) := by simp [hs']
        _ = ∏ i ∈ insert a s, μ (f i) := by
          simp [Finset.prod_insert, ha_notin]
  exact hs_all hf

end iIndep

/-! ## The hard direction: cut ⇒ noncontiguous -/

section CutToNoncontig

variable {q : ℕ}

/-! ### Helper lemmas on `IndexSeparated` -/

lemma IndexSeparated.symm {A B : Set ℤ} {k : ℕ} (h : IndexSeparated A B k) :
    IndexSeparated B A k := by
  intro b hb a ha
  have hab : Int.natAbs (a - b) > k := h (a := a) ha (b := b) hb
  have hswap : Int.natAbs (a - b) = Int.natAbs (b - a) := by
    have hEq : Int.natAbs (a - b) = Int.natAbs (-(a - b)) := by
      simpa using (Int.natAbs_neg (a - b)).symm
    have h' : -(a - b) = b - a := by abel
    exact hEq.trans (by simp [h'])
  simpa [hswap] using hab

lemma IndexSeparated.disjoint {A B : Set ℤ} {k : ℕ} (h : IndexSeparated A B k) : Disjoint A B := by
  refine Set.disjoint_left.2 ?_
  intro x hxA hxB
  have hk : Int.natAbs (x - x) > k := h (a := x) hxA (b := x) hxB
  simp at hk

/-! ### Converting `natAbs` bounds to ordered inequalities -/

private lemma add_lt_of_natAbs_sub_gt {a b : ℤ} {k : ℕ} (hab : a < b)
    (h : Int.natAbs (a - b) > k) : a + k < b := by
  have hk : (k : ℤ) < (Int.natAbs (a - b) : ℤ) := (Int.ofNat_lt.mpr h)
  have hk' : (k : ℤ) < |a - b| := by
    simpa [Int.natCast_natAbs] using hk
  have habs : |a - b| = b - a := by
    have hneg : a - b < 0 := (sub_neg).2 hab
    -- `|a-b| = -(a-b) = b-a`.
    simp [abs_of_neg hneg]
  have : (k : ℤ) < b - a := by simpa [habs] using hk'
  linarith

/-! ### Basic properties of `groupBySide` -/

private lemma groupBySide_snd_ne_nil (side : ℤ → Bool) :
    ∀ l : List ℤ, ∀ g ∈ groupBySide side l, g.2 ≠ [] := by
  intro l
  induction l with
  | nil =>
      intro g hg
      simp [groupBySide] at hg
  | cons x xs ih =>
      cases h : groupBySide side xs with
      | nil =>
          intro g hg
          have : g = (side x, [x]) := by simpa [groupBySide, h] using hg
          subst this
          simp
      | cons g0 gs =>
          rcases g0 with ⟨b', ys⟩
          by_cases hb : side x = b'
          · intro g hg
            have hg' : g = (b', x :: ys) ∨ g ∈ gs := by
              simpa [groupBySide, h, hb] using hg
            rcases hg' with rfl | hg'
            · simp
            · have : g ∈ groupBySide side xs := by
                have : g ∈ (b', ys) :: gs := List.mem_cons_of_mem _ hg'
                simpa [h] using this
              exact ih g this
          · intro g hg
            have hg' : g = (side x, [x]) ∨ g ∈ (b', ys) :: gs := by
              simpa [groupBySide, h, hb] using hg
            rcases hg' with rfl | hg'
            · simp
            · have : g ∈ groupBySide side xs := by simpa [h] using hg'
              exact ih g this

private lemma groupBySide_side_eq_fst (side : ℤ → Bool) :
    ∀ l : List ℤ, ∀ g ∈ groupBySide side l, ∀ z ∈ g.2, side z = g.1 := by
  intro l
  induction l with
  | nil =>
      intro g hg
      simp [groupBySide] at hg
  | cons x xs ih =>
      cases h : groupBySide side xs with
      | nil =>
          intro g hg z hz
          have : g = (side x, [x]) := by simpa [groupBySide, h] using hg
          subst this
          simp at hz
          subst hz
          simp
      | cons g0 gs =>
          rcases g0 with ⟨b', ys⟩
          by_cases hb : side x = b'
          · intro g hg z hz
            have hg' : g = (b', x :: ys) ∨ g ∈ gs := by
              simpa [groupBySide, h, hb] using hg
            rcases hg' with rfl | hg'
            · simp at hz
              rcases hz with rfl | hz
              · simp [hb]
              · have hy : (b', ys) ∈ groupBySide side xs := by simp [h]
                exact ih (b', ys) hy z hz
            · have : g ∈ groupBySide side xs := by
                have : g ∈ (b', ys) :: gs := List.mem_cons_of_mem _ hg'
                simpa [h] using this
              exact ih g this z hz
          · intro g hg z hz
            have hg' : g = (side x, [x]) ∨ g ∈ (b', ys) :: gs := by
              simpa [groupBySide, h, hb] using hg
            rcases hg' with rfl | hg'
            · simp at hz
              subst hz
              simp
            · have : g ∈ groupBySide side xs := by simpa [h] using hg'
              exact ih g this z hz

private lemma groupBySide_isChain_fst_ne (side : ℤ → Bool) :
    ∀ l : List ℤ, (groupBySide side l).IsChain (fun g₁ g₂ : Bool × List ℤ => g₁.1 ≠ g₂.1) := by
  intro l
  induction l with
  | nil =>
      simp [groupBySide]
  | cons x xs ih =>
      cases h : groupBySide side xs with
      | nil =>
          simp [groupBySide, h]
      | cons g0 gs =>
          rcases g0 with ⟨b', ys⟩
          by_cases hb : side x = b'
          · -- merged: `fst` sequence unchanged, only the list part changes.
            cases gs with
            | nil =>
                simp [groupBySide, h, hb]
            | cons g1 gs' =>
                have hchain : ((b', ys) :: g1 :: gs').IsChain
                    (fun g₁ g₂ : Bool × List ℤ => g₁.1 ≠ g₂.1) := by
                  simpa [h] using ih
                have hrel : (b', x :: ys).1 ≠ g1.1 := by
                  -- extract the head relation from `hchain`
                  have : (b', ys).1 ≠ g1.1 :=
                    (List.isChain_cons_cons.1 hchain).1
                  simpa using this
                have htail :
                    (g1 :: gs').IsChain (fun g₁ g₂ : Bool × List ℤ => g₁.1 ≠ g₂.1) :=
                  (List.isChain_cons_cons.1 hchain).2
                have hr :
                    (fun g₁ g₂ : Bool × List ℤ => g₁.1 ≠ g₂.1) (b', x :: ys) g1 := by
                  simpa using hrel
                simpa [groupBySide, h, hb] using
                  (List.IsChain.cons_cons (R := fun g₁ g₂ : Bool × List ℤ => g₁.1 ≠ g₂.1)
                    (a := (b', x :: ys)) (b := g1) (l := gs') hr htail)
          · -- not merged: new head chunk has different `fst` from the next one.
            have hrel : (side x, [x]).1 ≠ (b', ys).1 := by simp [hb]
            have htail :
                ((b', ys) :: gs).IsChain (fun g₁ g₂ : Bool × List ℤ => g₁.1 ≠ g₂.1) := by
              simpa [h] using ih
            have hr :
                (fun g₁ g₂ : Bool × List ℤ => g₁.1 ≠ g₂.1) (side x, [x]) (b', ys) := by
              simpa using hrel
            simpa [groupBySide, h, hb] using
              (List.IsChain.cons_cons (R := fun g₁ g₂ : Bool × List ℤ => g₁.1 ≠ g₂.1)
                (a := (side x, [x])) (b := (b', ys)) (l := gs) hr htail)

/-! ### Cut ⇒ noncontiguous for finite index sets -/

private lemma IndexSeparated.subset_left {A B A' : Set ℤ} {k : ℕ}
    (h : IndexSeparated A B k) (hA : A' ⊆ A) : IndexSeparated A' B k := by
  intro a ha b hb
  exact h (a := a) (hA ha) (b := b) hb

private lemma IndexSeparated.subset_right {A B B' : Set ℤ} {k : ℕ}
    (h : IndexSeparated A B k) (hB : B' ⊆ B) : IndexSeparated A B' k := by
  intro a ha b hb
  exact h (a := a) ha (b := b) (hB hb)

private lemma le_getLast_of_mem_of_isChain_lt {l : List ℤ} (hl : l.IsChain (fun a b : ℤ => a < b))
    {x : ℤ} (hx : x ∈ l) :
    x ≤ l.getLast (List.ne_nil_of_mem hx) := by
  classical
  set hne : l ≠ [] := List.ne_nil_of_mem hx
  set last : ℤ := l.getLast hne
  by_cases hxl : x = last
  · simp [hxl, last]
  · have hx_drop : x ∈ l.dropLast :=
      List.mem_dropLast_of_mem_of_ne_getLast hx (by simpa [last] using hxl)
    -- Reverse the chain to compare every element with `last`.
    have hrev : l.reverse.IsChain (fun a b : ℤ => b < a) := by
      exact (List.isChain_reverse (R := fun a b : ℤ => b < a) (l := l)).2 hl
    have hdecomp : l.reverse = last :: l.dropLast.reverse := by
      have : l = l.dropLast ++ [last] := by
        simpa [last] using (List.dropLast_append_getLast hne).symm
      -- reverse both sides
      calc
        l.reverse = (l.dropLast ++ [last]).reverse := by
          simpa using congrArg List.reverse this
        _ = [last] ++ l.dropLast.reverse := by simp [List.reverse_append]
        _ = last :: l.dropLast.reverse := rfl
    have hrev' : (last :: l.dropLast.reverse).IsChain (fun a b : ℤ => b < a) := by
      simpa [hdecomp] using hrev
    have hx_tail : x ∈ l.dropLast.reverse := by
      simpa using (List.mem_reverse.2 hx_drop)
    have hx_lt : x < last := hrev'.rel_cons (R := fun a b : ℤ => b < a) (a := last) (b := x) hx_tail
    exact le_of_lt hx_lt

/- The previous attempt at a finset proof was too brittle; keep it for reference but disabled. -/
/- 
private lemma indep_coordMeasurableSpace_finset_of_isKDependent {μ : ProbabilityMeasure (ℤ → Fin q)}
    {k : ℕ} (hcut : IsKDependent (q := q) μ k) {s t : Finset ℤ}
    (hst : IndexSeparated (A := (s : Set ℤ)) (B := (t : Set ℤ)) k) :
    Indep (coordMeasurableSpace (q := q) (s : Set ℤ)) (coordMeasurableSpace (q := q) (t : Set ℤ))
      (μ := (μ : Measure _)) := by
  classical
  -- Trivial cases: one side empty.
  by_cases hs : s = ∅
  · subst hs
    haveI : IsEmpty {j : ℤ // j ∈ (∅ : Set ℤ)} := ⟨fun j => by cases j.2⟩
    simpa [coordMeasurableSpace, FiniteDependence.coordMeasurableSpace, iSup_of_empty] using
      (ProbabilityTheory.indep_bot_left (μ := (μ : Measure (ℤ → Fin q)))
        (m' := coordMeasurableSpace (q := q) (t : Set ℤ)))
  by_cases ht : t = ∅
  · subst ht
    haveI : IsEmpty {j : ℤ // j ∈ (∅ : Set ℤ)} := ⟨fun j => by cases j.2⟩
    simpa [coordMeasurableSpace, FiniteDependence.coordMeasurableSpace, iSup_of_empty] using
      (ProbabilityTheory.indep_bot_right (μ := (μ : Measure (ℤ → Fin q)))
        (m' := coordMeasurableSpace (q := q) (s : Set ℤ)))

  -- Sort the (finite) union and group into alternating blocks by membership in `s`.
  let u : List ℤ := (s ∪ t).sort
  let side : ℤ → Bool := fun z => decide (z ∈ s)
  let groups : List (Bool × List ℤ) := groupBySide side u
  have hu : groups.flatMap (fun g => g.2) = u := bind_groupBySide_eq side u

  let n : ℕ := groups.length
  -- The σ-algebra generated by a block.
  let blockSet : Fin n → Set ℤ := fun i => {z : ℤ | z ∈ (groups.get i).2}
  let m : Fin n → MeasurableSpace (ℤ → Fin q) := fun i => coordMeasurableSpace (q := q) (blockSet i)

  -- Useful: every block list is nonempty.
  have hblock_ne_nil : ∀ i : Fin n, (groups.get i).2 ≠ [] := by
    intro i
    have hi : groups.get i ∈ groups := List.get_mem groups i
    -- unfold `groups`
    simpa [groups] using groupBySide_snd_ne_nil side u (g := groups.get i) (by simpa [groups] using hi)

  -- The underlying index sets `s` and `t` are disjoint.
  have hdisj : Disjoint (s : Set ℤ) (t : Set ℤ) := IndexSeparated.disjoint (A := (s : Set ℤ)) (B := (t : Set ℤ)) hst

  -- Successive independence of blocks gives mutual independence (`iIndep`) of the family `m`.
  have hm_iIndep : iIndep m (μ := (μ : Measure (ℤ → Fin q))) := by
    -- We apply `iIndep_of_indep_iSup_lt` on the linearly ordered index type `Fin n`.
    classical
    haveI : MeasureTheory.IsProbabilityMeasure (μ := (μ : Measure (ℤ → Fin q))) := inferInstance
    haveI : MeasureTheory.IsZeroOrProbabilityMeasure (μ := (μ : Measure (ℤ → Fin q))) := inferInstance
    refine iIndep_of_indep_iSup_lt (m := m) (μ := (μ : Measure (ℤ → Fin q))) ?_
    intro a
    by_cases ha0 : a.1 = 0
    · -- no previous blocks
      haveI : IsEmpty {b : Fin n // b < a} := by
        refine ⟨?_⟩
        rintro ⟨b, hb⟩
        -- `b < a` would force `b.1 < 0`.
        have : b.1 < a.1 := hb
        simpa [ha0] using this
      simpa using (ProbabilityTheory.indep_bot_right (μ := (μ : Measure (ℤ → Fin q))) (m' := m a))
    · -- choose a cut between the previous block `p = a-1` and the current block `a`.
      let pNat : ℕ := a.1 - 1
      have hp : pNat < n := by
        -- `a.1 - 1 ≤ a.1 < n`
        exact lt_of_le_of_lt (Nat.sub_le a.1 1) a.2
      let p : Fin n := ⟨pNat, hp⟩

      -- The previous and current blocks as list pieces.
      let prevList : List ℤ := (groups.get p).2
      let currList : List ℤ := (groups.get a).2
      have hprev_ne : prevList ≠ [] := by simpa [prevList] using hblock_ne_nil p
      have hcurr_ne : currList ≠ [] := by simpa [currList] using hblock_ne_nil a
      let lastPrev : ℤ := prevList.getLast hprev_ne
      let cut : ℤ := lastPrev + 1

      -- Decompose `groups` around the consecutive blocks `p` and `a`.
      have hap : pNat + 1 = a.1 := by
        -- `a.1 - 1 + 1 = a.1` since `a.1 ≠ 0`
        have ha1 : 1 ≤ a.1 := Nat.succ_le_iff.2 (Nat.pos_of_ne_zero ha0)
        simpa [pNat, Nat.sub_add_cancel ha1]
      have hdrop_p : groups.drop pNat = groups.get p :: groups.drop (pNat + 1) := by
        -- `drop_eq_getElem_cons` uses `getElem` (`l[n]`), rewrite via `get_eq_getElem`.
        have hpNat : pNat < groups.length := by simpa [n] using hp
        have := List.drop_eq_getElem_cons (l := groups) (n := pNat) hpNat
        -- rewrite `groups[pNat]` as `groups.get p`
        have hget : groups[pNat] = groups.get p := by
          -- `p.1 = pNat`
          simpa [p, pNat] using (List.get_eq_getElem (l := groups) (i := p)).symm
        simpa [hget] using this
      have hdrop_a : groups.drop a.1 = groups.get a :: groups.drop (a.1 + 1) := by
        have haNat : a.1 < groups.length := by simpa [n] using a.2
        have := List.drop_eq_getElem_cons (l := groups) (n := a.1) haNat
        have hget : groups[a.1] = groups.get a := by
          simpa using (List.get_eq_getElem (l := groups) (i := a)).symm
        simpa [hget] using this

      -- The list of all indices in blocks `< a` and in blocks `≥ a`.
      let prefixBlocks : List (Bool × List ℤ) := groups.take a.1
      let suffixBlocks : List (Bool × List ℤ) := groups.drop a.1
      let prefixList : List ℤ := prefixBlocks.flatMap (fun g => g.2)
      let suffixList : List ℤ := suffixBlocks.flatMap (fun g => g.2)

      have hgroups_split : groups = prefixBlocks ++ suffixBlocks := by
        simp [prefixBlocks, suffixBlocks, List.take_append_drop]
      have hu_split : u = prefixList ++ suffixList := by
        -- use `groups = take ++ drop` and flatten
        have : groups.flatMap (fun g => g.2) = prefixList ++ suffixList := by
          simp [prefixList, suffixList, hgroups_split]
        -- combine with `hu`
        simpa [prefixList, suffixList] using (hu.trans this)

      -- `u` is strictly increasing, hence a chain for `<`.
      have hchain_u : u.IsChain (· < ·) := (Finset.sortedLT_sort (s ∪ t)).isChain
      -- The prefix and suffix are chains as well.
      have hchain_prefix : prefixList.IsChain (· < ·) := by
        have : (prefixList ++ suffixList).IsChain (· < ·) := by simpa [hu_split] using hchain_u
        exact this.left_of_append
      have hchain_suffix : suffixList.IsChain (· < ·) := by
        have : (prefixList ++ suffixList).IsChain (· < ·) := by simpa [hu_split] using hchain_u
        exact this.right_of_append

      -- The last element of the prefix is `lastPrev`.
      have hlast_prefix : prefixList.getLast (by
          -- nonempty since `p` is included in `prefixBlocks`
          intro hnil
          have : prevList = [] := by
            -- `prevList` appears in `prefixList`, contradiction to `hprev_ne`
            simpa [prefixList, prefixBlocks, prevList] using hnil
          exact hprev_ne this) = lastPrev := by
        -- Identify `prefixBlocks = (groups.take pNat) ++ [groups.get p]`.
        have hpNat_lt : pNat < groups.length := by simpa [n] using hp
        have htake : groups.take a.1 = groups.take pNat ++ [groups.get p] := by
          -- `take_concat_get'` in forward direction.
          have ha1 : a.1 = pNat + 1 := hap.symm
          -- `groups.take pNat ++ [groups[pNat]] = groups.take (pNat+1)`
          have hconcat := (List.take_concat_get' (l := groups) (i := pNat) hpNat_lt)
          -- rewrite `groups[pNat]` as `groups.get p`
          have hget : groups[pNat] = groups.get p := by
            simpa [p, pNat] using (List.get_eq_getElem (l := groups) (i := p)).symm
          -- now rewrite `pNat+1` as `a.1`
          simpa [prefixBlocks, ha1, hget] using hconcat.symm
        -- Flatten and take `getLast`.
        have : prefixList = (groups.take pNat).flatMap (fun g => g.2) ++ prevList := by
          simp [prefixList, prefixBlocks, htake, prevList]
        -- Now `getLast` is the `getLast` of `prevList`.
        have : prefixList.getLast (by
            intro hnil
            have : prevList = [] := by
              -- if the append is empty, the right part is empty
              simpa [this] using congrArg List.length hnil
            exact hprev_ne this) = prevList.getLast hprev_ne := by
          -- use the standard lemma for `getLast` of an append.
          simpa [this] using
            (List.getLast_append_of_right_ne_nil ((groups.take pNat).flatMap (fun g => g.2)) prevList hprev_ne)
        simpa [lastPrev, prevList] using this

      -- Show block `a` lies in the future half-line `≥ cut + k`.
      have hblock_a_le_future : m a ≤ futureMeasurableSpace (q := q) cut k := by
        -- it suffices to show inclusion of index sets
        have : blockSet a ⊆ {j : ℤ | cut + k ≤ j} := by
          intro z hz
          -- `z` is in the suffix, so it is after `lastPrev` in the increasing list.
          have hz_suffix : z ∈ suffixList := by
            -- `currList ⊆ suffixList`
            have ha_mem : groups.get a ∈ suffixBlocks := by
              -- `a` is the first element of `suffixBlocks`
              have : suffixBlocks = groups.get a :: groups.drop (a.1 + 1) := by
                simpa [suffixBlocks] using hdrop_a
              simpa [suffixBlocks, this] using (List.mem_cons_self _ _)
            -- `z ∈ currList`
            have hz_curr : z ∈ currList := by simpa [blockSet, currList] using hz
            exact List.mem_flatMap.2 ⟨groups.get a, ha_mem, hz_curr⟩
          -- Build a chain starting at `lastPrev`.
          have hprefix_ne : prefixList ≠ [] := by
            -- `prefixBlocks` contains `groups.get p`
            intro hnil
            have : prevList = [] := by
              -- from `prefixList = prefixFlat ++ prevList`
              simpa [prefixList, prefixBlocks, prevList] using hnil
            exact hprev_ne this
          -- `prefixList = dropLast ++ [lastPrev]`
          have hdecomp : prefixList.dropLast ++ [prefixList.getLast hprefix_ne] = prefixList :=
            List.dropLast_append_getLast hprefix_ne
          have hdecomp' : prefixList = prefixList.dropLast ++ [lastPrev] := by
            -- rewrite the `getLast`
            simpa [hlast_prefix] using hdecomp.symm
          -- Thus `u = (prefixList.dropLast) ++ (lastPrev :: suffixList)` and we can use transitivity.
          have hu' : u = prefixList.dropLast ++ (lastPrev :: suffixList) := by
            calc
              u = (prefixList ++ suffixList) := by simpa [hu_split]
              _ = (prefixList.dropLast ++ [lastPrev]) ++ suffixList := by
                simpa [hdecomp'] using congrArg (fun l => l ++ suffixList) rfl
              _ = prefixList.dropLast ++ (lastPrev :: suffixList) := by simp [List.append_assoc]
          have hchain_tail : (lastPrev :: suffixList).IsChain (· < ·) := by
            have : (prefixList.dropLast ++ (lastPrev :: suffixList)).IsChain (· < ·) := by
              simpa [hu'] using hchain_u
            exact this.right_of_append
          have hz_lt : lastPrev < z := by
            -- `z ∈ suffixList`
            exact hchain_tail.rel_cons (R := (· < ·)) (a := lastPrev) (b := z) hz_suffix
          -- Apply separation to get `lastPrev + k < z`.
          have hnatAbs : Int.natAbs (lastPrev - z) > k := by
            -- Determine which side `lastPrev` and `z` lie on.
            have hfst_ne : (groups.get p).1 ≠ (groups.get a).1 := by
              -- consecutive blocks have different `fst`
              have hchain_g : (groupBySide side u).IsChain (fun g₁ g₂ : Bool × List ℤ => g₁.1 ≠ g₂.1) :=
                groupBySide_isChain_fst_ne side u
              -- `groups.drop pNat` starts with `p` then `a`
              have : (groups.drop pNat).IsChain (fun g₁ g₂ : Bool × List ℤ => g₁.1 ≠ g₂.1) := by
                simpa [groups] using hchain_g.drop pNat
              -- extract the head relation
              have hrel : (groups.get p).1 ≠ (groups.get a).1 := by
                -- using the explicit shape of the dropped list
                have hshape : groups.drop pNat = groups.get p :: groups.get a :: groups.drop (a.1 + 1) := by
                  -- combine `hdrop_p` and `hdrop_a`, using `hap`
                  have : groups.drop pNat = groups.get p :: groups.drop a.1 := by simpa [suffixBlocks, hap] using hdrop_p
                  -- now expand `groups.drop a.1`
                  simpa [this, hdrop_a]
                -- rewrite and use `isChain_cons_cons`
                simpa [hshape] using (List.isChain_cons_cons.1 this).1
              exact hrel

            -- Membership in `s` for elements in a block is constant.
            have hside_prev : side lastPrev = (groups.get p).1 := by
              have hp_mem : groups.get p ∈ groups := List.get_mem groups p
              have hmem : (groups.get p) ∈ groupBySide side u := by simpa [groups] using hp_mem
              have : lastPrev ∈ (groups.get p).2 := by
                have : lastPrev ∈ prevList := List.getLast_mem hprev_ne
                simpa [prevList] using this
              exact groupBySide_side_eq_fst side u (g := groups.get p) hmem lastPrev this
            have hside_curr : side z = (groups.get a).1 := by
              have ha_mem : groups.get a ∈ groups := List.get_mem groups a
              have hmem : (groups.get a) ∈ groupBySide side u := by simpa [groups] using ha_mem
              have hz_mem : z ∈ (groups.get a).2 := by
                have : z ∈ currList := by simpa [currList] using (show z ∈ (groups.get a).2 from hz)
                simpa [currList] using this
              exact groupBySide_side_eq_fst side u (g := groups.get a) hmem z hz_mem

            have lastPrev_mem_union : lastPrev ∈ (s ∪ t) := by
              -- from membership in `u`
              have : lastPrev ∈ u := by
                -- `lastPrev ∈ prevList ⊆ u`
                have hprev_in_u : prevList ⊆ u := by
                  intro x hx
                  -- via flatten
                  have : x ∈ groups.flatMap (fun g => g.2) := by
                    have hp_mem : groups.get p ∈ groups := List.get_mem groups p
                    exact List.mem_flatMap.2 ⟨groups.get p, hp_mem, by simpa [prevList] using hx⟩
                  simpa [hu] using this
                exact hprev_in_u _ (List.getLast_mem hprev_ne)
              simpa [u] using (Finset.mem_sort (r := (· ≤ ·)) (s := s ∪ t) (a := lastPrev)).1 this

            have z_mem_union : z ∈ (s ∪ t) := by
              have : z ∈ u := by
                -- `z ∈ currList ⊆ u`
                have hcurr_in_u : currList ⊆ u := by
                  intro x hx
                  have : x ∈ groups.flatMap (fun g => g.2) := by
                    have ha_mem : groups.get a ∈ groups := List.get_mem groups a
                    exact List.mem_flatMap.2 ⟨groups.get a, ha_mem, by simpa [currList] using hx⟩
                  simpa [hu] using this
                exact hcurr_in_u _ (by simpa [currList] using hz)
              simpa [u] using (Finset.mem_sort (r := (· ≤ ·)) (s := s ∪ t) (a := z)).1 this

            -- Convert the boolean `side` info into membership in `s`/`t`.
            have lastPrev_mem_s : lastPrev ∈ (s : Set ℤ) ↔ (groups.get p).1 = true := by
              -- `side lastPrev = decide (lastPrev ∈ s)`
              have : decide (lastPrev ∈ s) = (groups.get p).1 := by simpa [side] using hside_prev
              constructor
              · intro hmem
                have : decide (lastPrev ∈ s) = true := by simpa using (decide_eq_true_eq.mpr hmem)
                -- turn into bool equality
                simpa [this] using this
              · intro hb
                have : decide (lastPrev ∈ s) = true := by simpa [hb] using this.symm
                exact (decide_eq_true_eq.mp this)

            have z_mem_s : z ∈ (s : Set ℤ) ↔ (groups.get a).1 = true := by
              have : decide (z ∈ s) = (groups.get a).1 := by simpa [side] using hside_curr
              constructor
              · intro hmem
                have : decide (z ∈ s) = true := by simpa using (decide_eq_true_eq.mpr hmem)
                simpa [this] using this
              · intro hb
                have : decide (z ∈ s) = true := by simpa [hb] using this.symm
                exact (decide_eq_true_eq.mp this)

            -- Determine which set each element is in.
            have lastPrev_mem_t : lastPrev ∈ (t : Set ℤ) ↔ (groups.get p).1 = false := by
              constructor
              · intro htmem
                -- if it were in `s`, we'd contradict disjointness
                have : lastPrev ∉ (s : Set ℤ) := by
                  intro hs'
                  exact (Set.disjoint_left.1 hdisj hs' htmem)
                -- hence decide is false
                have : decide (lastPrev ∈ s) = false := by simpa using (decide_eq_false_eq.mpr this)
                -- use `side` info
                have : (groups.get p).1 = false := by
                  -- `side lastPrev = (groups.get p).1`
                  have hside : side lastPrev = (groups.get p).1 := by simpa [side] using hside_prev
                  simpa [side, this] using hside
                simpa [this]
              · intro hb
                -- `lastPrev ∈ s ∪ t` and not in `s`, so in `t`.
                have : lastPrev ∉ (s : Set ℤ) := by
                  intro hs'
                  have : (groups.get p).1 = true := (lastPrev_mem_s).1 hs'
                  simpa [hb] using this
                have : lastPrev ∈ (t : Set ℤ) := by
                  have : lastPrev ∈ (s ∪ t : Set ℤ) := by simpa using lastPrev_mem_union
                  rcases this with hs' | ht'
                  · exact (this hs').elim
                  · exact ht'
                exact this

            have z_mem_t : z ∈ (t : Set ℤ) ↔ (groups.get a).1 = false := by
              constructor
              · intro htmem
                have : z ∉ (s : Set ℤ) := by
                  intro hs'
                  exact (Set.disjoint_left.1 hdisj hs' htmem)
                have : decide (z ∈ s) = false := by simpa using (decide_eq_false_eq.mpr this)
                have hside : side z = (groups.get a).1 := by simpa [side] using hside_curr
                have : (groups.get a).1 = false := by simpa [side, this] using hside
                simpa [this]
              · intro hb
                have : z ∉ (s : Set ℤ) := by
                  intro hs'
                  have : (groups.get a).1 = true := (z_mem_s).1 hs'
                  simpa [hb] using this
                have : z ∈ (t : Set ℤ) := by
                  have : z ∈ (s ∪ t : Set ℤ) := by simpa using z_mem_union
                  rcases this with hs' | ht'
                  · exact (this hs').elim
                  · exact ht'
                exact this

            -- Now apply `hst` in the appropriate direction.
            by_cases hcurrBool : (groups.get a).1 = true
            · -- `z ∈ s`, so `lastPrev ∈ t` and use symmetry.
              have hzS : z ∈ (s : Set ℤ) := (z_mem_s).2 hcurrBool
              have hpBool : (groups.get p).1 = false := by
                cases hbPrev : (groups.get p).1 <;> cases hcurrBool' : (groups.get a).1 <;> simp at *
              have hlastT : lastPrev ∈ (t : Set ℤ) := (lastPrev_mem_t).2 hpBool
              have hst' : IndexSeparated (t : Set ℤ) (s : Set ℤ) k := IndexSeparated.symm (A := (s : Set ℤ)) (B := (t : Set ℤ)) hst
              simpa [sub_eq_add_neg, add_comm, add_left_comm, add_assoc] using
                hst' (a := lastPrev) hlastT (b := z) hzS
            · -- `z ∈ t`, so `lastPrev ∈ s` and use `hst`.
              have hzT : z ∈ (t : Set ℤ) := by
                have : (groups.get a).1 = false := by
                  cases hb : (groups.get a).1 <;> simp at hcurrBool ⊢; rfl
                exact (z_mem_t).2 this
              have hpBool : (groups.get p).1 = true := by
                -- since bools differ, prev must be true
                cases hbPrev : (groups.get p).1 <;> cases hbCurr : (groups.get a).1 <;> simp at hfst_ne hcurrBool hbCurr hbPrev
              have hlastS : lastPrev ∈ (s : Set ℤ) := (lastPrev_mem_s).2 hpBool
              simpa using hst (a := lastPrev) hlastS (b := z) hzT

          -- Convert the strict inequality into the desired `≤`.
          have hklt : lastPrev + (k : ℤ) < z := add_lt_of_natAbs_sub_gt hz_lt hnatAbs
          have hkle : lastPrev + (k : ℤ) + 1 ≤ z := Int.add_one_le_of_lt hklt
          -- `cut + k = lastPrev + 1 + k = lastPrev + k + 1`.
          simpa [cut, add_assoc, add_left_comm, add_comm] using hkle
        -- conclude by monotonicity of coordinate σ-algebras
        exact coordMeasurableSpace_mono (q := q) this

      -- Show the σ-algebra from previous blocks lies in the past half-line `< cut`.
      have hprev_le_past : (⨆ b : {b : Fin n // b < a}, m b.1) ≤ pastMeasurableSpace (q := q) cut := by
        refine iSup_le ?_
        rintro ⟨b, hb⟩
        -- it suffices to show all indices in block `b` are `< cut`
        have : blockSet b ⊆ {j : ℤ | j < cut} := by
          intro z hz
          -- `z` lies in the prefix list, hence `z ≤ lastPrev`.
          have hz_prefix : z ∈ prefixList := by
            -- show `groups.get b ∈ prefixBlocks`
            have hbNat : b.1 < a.1 := hb
            have hb_len : b.1 < prefixBlocks.length := by
              -- `prefixBlocks.length = a.1` since `a.1 ≤ groups.length`
              have ha_le : a.1 ≤ groups.length := Nat.le_of_lt a.2
              simpa [prefixBlocks, List.length_take, Nat.min_eq_left ha_le] using hbNat
            have hb_mem : groups.get b ∈ prefixBlocks := by
              -- `prefixBlocks[b] = groups[b] = groups.get b`
              have htake : (prefixBlocks : List (Bool × List ℤ))[b.1] = groups[b.1] := by
                -- `getElem_take` form
                have : (prefixBlocks : List (Bool × List ℤ))[b.1] = groups[b.1] := by
                  -- `List.getElem_take` needs a bound in the taken list.
                  simpa [prefixBlocks] using (List.getElem_take (xs := groups) (j := a.1) (i := b.1))
                simpa using this
              have hgetb : groups[b.1] = groups.get b := by
                simpa using (List.get_eq_getElem (l := groups) (i := b)).symm
              -- membership via `getElem_mem`
              have : (prefixBlocks : List (Bool × List ℤ))[b.1] ∈ prefixBlocks := List.getElem_mem hb_len
              simpa [htake, hgetb] using this
            -- now use `mem_flatMap`
            have hz_block : z ∈ (groups.get b).2 := by simpa [blockSet] using hz
            exact List.mem_flatMap.2 ⟨groups.get b, hb_mem, hz_block⟩

          -- Compare to the last element using the reverse chain trick.
          have hprefix_ne : prefixList ≠ [] := by
            -- `prefixBlocks` includes `groups.get p`
            intro hnil
            have : prevList = [] := by
              -- from the `take` decomposition, the last block list must be empty
              simpa [prefixList, prefixBlocks, prevList] using hnil
            exact hprev_ne this
          have hz_le : z ≤ prefixList.getLast hprefix_ne := by
            -- any element is ≤ the last element in a strictly increasing chain
            -- (use reverse chain to obtain `<` and then `≤`)
            by_cases hzeq : z = prefixList.getLast hprefix_ne
            · simpa [hzeq]
            · have hz_drop : z ∈ prefixList.dropLast :=
                List.mem_dropLast_of_mem_of_ne_getLast hz_prefix (by simpa [hzeq])
              have hrev : prefixList.reverse.IsChain (fun x y : ℤ => y < x) := by
                -- apply `isChain_reverse`
                exact (List.isChain_reverse (R := fun x y : ℤ => y < x) (l := prefixList)).2 hchain_prefix
              -- rewrite the reverse as `last :: dropLast.reverse`
              have hdecomp : prefixList.reverse = prefixList.getLast hprefix_ne :: prefixList.dropLast.reverse := by
                have : prefixList.dropLast ++ [prefixList.getLast hprefix_ne] = prefixList :=
                  List.dropLast_append_getLast hprefix_ne
                -- reverse both sides
                have := congrArg List.reverse this.symm
                simpa [List.reverse_append, List.reverse_cons, List.reverse_nil] using this
              -- `z` is in the tail of the reverse.
              have hz_tail : z ∈ prefixList.dropLast.reverse := by
                simpa using (List.mem_reverse.2 hz_drop)
              have hz_lt : z < prefixList.getLast hprefix_ne := by
                -- apply `rel_cons` on the reversed chain
                have hrev' : (prefixList.getLast hprefix_ne :: prefixList.dropLast.reverse).IsChain (fun x y : ℤ => y < x) := by
                  simpa [hdecomp] using hrev
                exact hrev'.rel_cons (R := fun x y : ℤ => y < x) (a := prefixList.getLast hprefix_ne) (b := z) hz_tail
              exact le_of_lt hz_lt

          -- `prefixList.getLast = lastPrev` and hence `z < cut`.
          have hlast : prefixList.getLast hprefix_ne = lastPrev := by
            -- this is exactly `hlast_prefix`, after rewriting nonemptiness proofs
            simpa [hprefix_ne] using hlast_prefix
          have : z ≤ lastPrev := by simpa [hlast] using hz_le
          exact Int.lt_add_one_of_le (by simpa [cut] using this)
        exact coordMeasurableSpace_mono (q := q) this

      -- Now apply the cut independence and restrict to the relevant σ-algebras.
      have hind_cut : Indep (pastMeasurableSpace (q := q) cut) (futureMeasurableSpace (q := q) cut k)
          (μ := (μ : Measure (ℤ → Fin q))) := hcut cut
      have hind1 : Indep (pastMeasurableSpace (q := q) cut) (m a) (μ := (μ : Measure (ℤ → Fin q))) :=
        ProbabilityTheory.indep_of_indep_of_le_right hind_cut hblock_a_le_future
      have hind2 : Indep (m a) (pastMeasurableSpace (q := q) cut) (μ := (μ : Measure (ℤ → Fin q))) :=
        hind1.symm
      exact ProbabilityTheory.indep_of_indep_of_le_right hind2 hprev_le_past

  -- Split the blocks into those coming from `s` and those coming from `t`.
  let Strue : Set (Fin n) := {i | (groups.get i).1 = true}
  let Sfalse : Set (Fin n) := {i | (groups.get i).1 = false}
  have hST : Disjoint Strue Sfalse := by
    refine Set.disjoint_left.2 ?_
    intro i hiT hiF
    exact Bool.true_ne_false (hiT.trans hiF.symm)

  have hind_blocks : Indep (⨆ i ∈ Strue, m i) (⨆ i ∈ Sfalse, m i) (μ := (μ : Measure (ℤ → Fin q))) := by
    have h_le : ∀ i : Fin n, m i ≤ (MeasurableSpace.pi : MeasurableSpace (ℤ → Fin q)) := by
      intro i
      exact coordMeasurableSpace_le_pi (q := q) (blockSet i)
    exact ProbabilityTheory.indep_iSup_of_disjoint (m := m) (μ := (μ : Measure (ℤ → Fin q))) h_le hm_iIndep hST

  -- `coordMeasurableSpace s` is contained in the supremum of `s`-blocks.
  have hcoord_s_le : coordMeasurableSpace (q := q) (s : Set ℤ) ≤ ⨆ i ∈ Strue, m i := by
    classical
    refine iSup_le ?_
    rintro ⟨j, hj⟩
    -- `j` appears in the sorted union list, hence in some block.
    have hj_union : j ∈ (s ∪ t) := Or.inl hj
    have hj_u : j ∈ u := by
      -- `mem_sort` for finsets
      simpa [u] using (Finset.mem_sort (r := (· ≤ ·)) (s := s ∪ t) (a := j)).2 hj_union
    have hj_flat : j ∈ groups.flatMap (fun g => g.2) := by simpa [hu] using hj_u
    rcases List.mem_flatMap.1 hj_flat with ⟨g, hg_groups, hjg⟩
    -- identify the block index
    obtain ⟨i, rfl⟩ : ∃ i : Fin n, groups.get i = g := by
      have : g ∈ groups := hg_groups
      rcases List.mem_iff_get.1 this with ⟨i, rfl⟩
      exact ⟨i, rfl⟩
    have hiT : i ∈ Strue := by
      -- membership in `s` forces `side j = true`, hence the block boolean is `true`.
      have hgmem : groups.get i ∈ groupBySide side u := by simpa [groups] using List.get_mem groups i
      have hside : side j = (groups.get i).1 :=
        groupBySide_side_eq_fst side u (g := groups.get i) (by simpa [groups] using List.get_mem groups i) j hjg
      have : side j = true := by simpa [side] using (decide_eq_true_eq.mpr hj)
      have : (groups.get i).1 = true := by simpa [this] using hside.symm
      exact this
    have hj_block : j ∈ blockSet i := by simpa [blockSet] using hjg
    -- coordinate at `j` is measurable w.r.t. the block σ-algebra.
    have hcomap_le : MeasurableSpace.comap (fun x : ℤ → Fin q => x j) inferInstance ≤ m i := by
      -- `j` is one of the generators
      exact le_iSup (fun j : {j : ℤ // j ∈ blockSet i} =>
        MeasurableSpace.comap (fun x : ℤ → Fin q => x j.1) inferInstance) ⟨j, hj_block⟩
    -- and `m i` is below the supremum over `Strue`.
    have hmi_le : m i ≤ ⨆ i ∈ Strue, m i := by
      refine le_trans ?_ (le_iSup (fun i : Fin n => ⨆ (_ : i ∈ Strue), m i) i)
      exact le_iSup (fun _ : i ∈ Strue => m i) hiT
    exact le_trans hcomap_le hmi_le

  -- similarly for `t`-blocks
  have hcoord_t_le : coordMeasurableSpace (q := q) (t : Set ℤ) ≤ ⨆ i ∈ Sfalse, m i := by
    classical
    refine iSup_le ?_
    rintro ⟨j, hj⟩
    have hj_union : j ∈ (s ∪ t) := Or.inr hj
    have hj_u : j ∈ u := by
      simpa [u] using (Finset.mem_sort (r := (· ≤ ·)) (s := s ∪ t) (a := j)).2 hj_union
    have hj_flat : j ∈ groups.flatMap (fun g => g.2) := by simpa [hu] using hj_u
    rcases List.mem_flatMap.1 hj_flat with ⟨g, hg_groups, hjg⟩
    obtain ⟨i, rfl⟩ : ∃ i : Fin n, groups.get i = g := by
      have : g ∈ groups := hg_groups
      rcases List.mem_iff_get.1 this with ⟨i, rfl⟩
      exact ⟨i, rfl⟩
    have hiF : i ∈ Sfalse := by
      have hside : side j = (groups.get i).1 :=
        groupBySide_side_eq_fst side u (g := groups.get i) (by simpa [groups] using List.get_mem groups i) j hjg
      have : side j = false := by
        -- `j ∉ s` since `s` and `t` are disjoint
        have : j ∉ (s : Set ℤ) := by
          intro hs'
          exact (Set.disjoint_left.1 hdisj hs' hj)
        simpa [side] using (decide_eq_false_eq.mpr this)
      have : (groups.get i).1 = false := by simpa [this] using hside.symm
      exact this
    have hj_block : j ∈ blockSet i := by simpa [blockSet] using hjg
    have hcomap_le : MeasurableSpace.comap (fun x : ℤ → Fin q => x j) inferInstance ≤ m i := by
      exact le_iSup (fun j : {j : ℤ // j ∈ blockSet i} =>
        MeasurableSpace.comap (fun x : ℤ → Fin q => x j.1) inferInstance) ⟨j, hj_block⟩
    have hmi_le : m i ≤ ⨆ i ∈ Sfalse, m i := by
      refine le_trans ?_ (le_iSup (fun i : Fin n => ⨆ (_ : i ∈ Sfalse), m i) i)
      exact le_iSup (fun _ : i ∈ Sfalse => m i) hiF
    exact le_trans hcomap_le hmi_le

  -- Restrict block independence to `s` and `t`.
  exact
    ProbabilityTheory.indep_of_indep_of_le_left
      (ProbabilityTheory.indep_of_indep_of_le_right hind_blocks hcoord_t_le)
      hcoord_s_le
-/

private lemma indep_coordMeasurableSpace_finset_of_isKDependent {μ : ProbabilityMeasure (ℤ → Fin q)}
    {k : ℕ} (hcut : IsKDependent (q := q) μ k) {s t : Finset ℤ}
    (hst : IndexSeparated (A := (s : Set ℤ)) (B := (t : Set ℤ)) k) :
    Indep (coordMeasurableSpace (q := q) (s : Set ℤ)) (coordMeasurableSpace (q := q) (t : Set ℤ))
      (μ := (μ : Measure _)) := by
  classical
  haveI : MeasureTheory.IsProbabilityMeasure (μ := (μ : Measure (ℤ → Fin q))) := inferInstance
  haveI : MeasureTheory.IsZeroOrProbabilityMeasure (μ := (μ : Measure (ℤ → Fin q))) := inferInstance

  -- Trivial cases: one side empty.
  by_cases hs : s = ∅
  · subst hs
    haveI : IsEmpty {j : ℤ // j ∈ (∅ : Set ℤ)} := ⟨fun j => by cases j.2⟩
    simpa [coordMeasurableSpace, FiniteDependence.coordMeasurableSpace, iSup_of_empty] using
      (ProbabilityTheory.indep_bot_left (μ := (μ : Measure (ℤ → Fin q)))
        (m' := coordMeasurableSpace (q := q) (t : Set ℤ)))
  by_cases ht : t = ∅
  · subst ht
    haveI : IsEmpty {j : ℤ // j ∈ (∅ : Set ℤ)} := ⟨fun j => by cases j.2⟩
    simpa [coordMeasurableSpace, FiniteDependence.coordMeasurableSpace, iSup_of_empty] using
      (ProbabilityTheory.indep_bot_right (μ := (μ : Measure (ℤ → Fin q)))
        (m' := coordMeasurableSpace (q := q) (s : Set ℤ)))

  have hdisj : Disjoint (s : Set ℤ) (t : Set ℤ) :=
    IndexSeparated.disjoint (A := (s : Set ℤ)) (B := (t : Set ℤ)) hst

  -- Sort the union and group into alternating blocks by membership in `s`.
  let u : List ℤ := (s ∪ t).sort
  let side : ℤ → Bool := fun z => decide (z ∈ s)
  let groups : List (Bool × List ℤ) := groupBySide side u
  have hu : groups.flatMap (fun g => g.2) = u := bind_groupBySide_eq side u

  let n : ℕ := groups.length
  let blockSet : Fin n → Set ℤ := fun i => {z : ℤ | z ∈ (groups.get i).2}
  let m : Fin n → MeasurableSpace (ℤ → Fin q) := fun i => coordMeasurableSpace (q := q) (blockSet i)

  have hblock_ne_nil : ∀ i : Fin n, (groups.get i).2 ≠ [] := by
    intro i
    have hi : groups.get i ∈ groupBySide side u := by
      simp [groups]
    exact groupBySide_snd_ne_nil side u (g := groups.get i) hi

  have hchain_u : u.IsChain (fun a b : ℤ => a < b) := (Finset.sortedLT_sort (s ∪ t)).isChain

  -- Define the block index sets selecting blocks coming from `s` vs `t`.
  let Strue : Set (Fin n) := {i | (groups.get i).1 = true}
  let Sfalse : Set (Fin n) := {i | (groups.get i).1 = false}

  -- Mutual independence of all blocks.
  have hm_iIndep : iIndep m (μ := (μ : Measure (ℤ → Fin q))) := by
    classical
    refine iIndep_of_indep_iSup_lt (m := m) (μ := (μ : Measure (ℤ → Fin q))) ?_
    intro a
    by_cases ha0 : a.1 = 0
    · haveI : IsEmpty {b : Fin n // b < a} := by
        refine ⟨?_⟩
        rintro ⟨b, hb⟩
        have hb' : b.1 < a.1 := hb
        simp [ha0] at hb'
      simpa [iSup_of_empty] using
        (ProbabilityTheory.indep_bot_right (μ := (μ : Measure (ℤ → Fin q))) (m' := m a))
    · -- previous block index `p = a - 1`
      let pNat : ℕ := a.1 - 1
      have hp : pNat < n := lt_of_le_of_lt (Nat.sub_le a.1 1) a.2
      let p : Fin n := ⟨pNat, hp⟩

      let prevList : List ℤ := (groups.get p).2
      let currList : List ℤ := (groups.get a).2
      have hprev_ne : prevList ≠ [] := by simpa [prevList] using hblock_ne_nil p
      have hcurr_ne : currList ≠ [] := by simpa [currList] using hblock_ne_nil a
      let lastPrev : ℤ := prevList.getLast hprev_ne
      let headCurr : ℤ := currList.head hcurr_ne
      let cut : ℤ := lastPrev + 1

      -- Split `u` into the flattening of blocks `< a` and `≥ a`.
      let prefixBlocks : List (Bool × List ℤ) := groups.take a.1
      let suffixBlocks : List (Bool × List ℤ) := groups.drop a.1
      let prefixList : List ℤ := prefixBlocks.flatMap (fun g => g.2)
      let suffixList : List ℤ := suffixBlocks.flatMap (fun g => g.2)
      have hu_split : u = prefixList ++ suffixList := by
        have hflat :
            groups.flatMap (fun g => g.2) =
              (groups.take a.1).flatMap (fun g => g.2) ++ (groups.drop a.1).flatMap (fun g => g.2) := by
          have htd :
              (groups.take a.1 ++ groups.drop a.1).flatMap (fun g => g.2) = groups.flatMap (fun g => g.2) :=
            congrArg (fun l => l.flatMap (fun g => g.2)) (List.take_append_drop a.1 groups)
          have htd' :
              (groups.take a.1).flatMap (fun g => g.2) ++ (groups.drop a.1).flatMap (fun g => g.2) =
                groups.flatMap (fun g => g.2) := by
            have htd'' := htd
            rw [List.flatMap_append] at htd''
            exact htd''
          exact htd'.symm
        simpa [prefixList, suffixList, prefixBlocks, suffixBlocks] using hu.symm.trans hflat

      have hchain_full : (prefixList ++ suffixList).IsChain (fun a b : ℤ => a < b) := by
        simpa [hu_split] using hchain_u
      have hchain_prefix : prefixList.IsChain (fun a b : ℤ => a < b) := hchain_full.left_of_append
      have hchain_suffix : suffixList.IsChain (fun a b : ℤ => a < b) := hchain_full.right_of_append

      -- Describe the prefix blocks as `... ++ [p]`, and the suffix blocks as `a :: ...`.
      have hap : pNat + 1 = a.1 := by
        have ha1 : 1 ≤ a.1 := Nat.succ_le_iff.2 (Nat.pos_of_ne_zero ha0)
        simp [pNat, Nat.sub_add_cancel ha1]

      have hpNat_lt : pNat < groups.length := by simpa [n] using hp
      have hprefixBlocks :
          prefixBlocks = (groups.take pNat) ++ [groups.get p] := by
        -- `take_concat_get'` gives `take pNat ++ [groups[pNat]] = take (pNat+1)`
        have hconcat := List.take_concat_get' (l := groups) (i := pNat) hpNat_lt
        have hget : groups[pNat] = groups.get p := by
          simp [p, pNat]
        -- rewrite `pNat+1` as `a.1`
        simpa [prefixBlocks, hap, hget] using hconcat.symm

      have haNat : a.1 < groups.length := by
        exact a.2
      have hdrop_a : suffixBlocks = groups.get a :: groups.drop (a.1 + 1) := by
        have h := List.drop_eq_getElem_cons (l := groups) (i := a.1) haNat
        have hget : groups[a.1] = groups.get a :=
          (List.get_eq_getElem (l := groups) (i := a)).symm
        dsimp [suffixBlocks]
        exact h.trans (congrArg (fun x => x :: groups.drop (a.1 + 1)) hget)

      have hprefixList : prefixList = (groups.take pNat).flatMap (fun g => g.2) ++ prevList := by
        simp [prefixList, prefixBlocks, hprefixBlocks, prevList]
      have hsuffixList : suffixList = currList ++ (groups.drop (a.1 + 1)).flatMap (fun g => g.2) := by
        have hdrop_a' : groups.drop a.1 = groups.get a :: groups.drop (a.1 + 1) := by
          have hdrop_a' := hdrop_a
          dsimp [suffixBlocks] at hdrop_a'
          exact hdrop_a'
        dsimp [suffixList, suffixBlocks, currList]
        rw [hdrop_a']
        rfl

      -- `lastPrev` is the last element of `prefixList` and `headCurr` is the first of `suffixList`.
      have hlast_mem : lastPrev ∈ prefixList.getLast? := by
        have : lastPrev ∈ prevList.getLast? := by
          simp [lastPrev, List.getLast?_eq_some_getLast hprev_ne]
        -- propagate through the prefix append decomposition
        simpa [hprefixList] using List.mem_getLast?_append_of_mem_getLast? (l₁ := (groups.take pNat).flatMap (fun g => g.2))
          (l₂ := prevList) this
      have hhead_mem : headCurr ∈ suffixList.head? := by
        -- `suffixList` starts with `currList`
        have : headCurr ∈ currList.head? := by
          cases hcurr : currList with
          | nil =>
              cases (hcurr_ne hcurr)
          | cons x xs =>
              simp [headCurr, hcurr]
        -- `head?` of an append with nonempty left side
        simpa [hsuffixList] using List.mem_head?_append_of_mem_head? (s := currList) (t := (groups.drop (a.1 + 1)).flatMap (fun g => g.2)) this

      have hlt : lastPrev < headCurr := by
        -- extract the boundary relation from the chain append characterization
        exact (List.isChain_append.1 hchain_full).2.2 _ hlast_mem _ hhead_mem

      -- Determine which of `s` and `t` each boundary element lies in, to get `natAbs` separation.
      have hfst_ne : (groups.get p).1 ≠ (groups.get a).1 := by
        have hchain_g : (groupBySide side u).IsChain (fun g₁ g₂ : Bool × List ℤ => g₁.1 ≠ g₂.1) :=
          groupBySide_isChain_fst_ne side u
        have : (groups.drop pNat).IsChain (fun g₁ g₂ : Bool × List ℤ => g₁.1 ≠ g₂.1) := by
          simpa [groups] using hchain_g.drop pNat
        -- `groups.drop pNat` starts with `p` then `a`
        have hshape : groups.drop pNat = groups.get p :: groups.get a :: groups.drop (a.1 + 1) := by
          -- combine `hconcat` for `drop` and `hdrop_a`
          have h1 : groups.drop pNat = groups.get p :: groups.drop (pNat + 1) := by
            have h := List.drop_eq_getElem_cons (l := groups) (i := pNat) hpNat_lt
            have hget : groups[pNat] = groups.get p := by
              simp [p, pNat]
            simpa [hget] using h
          have h2 : groups.drop (pNat + 1) = groups.get a :: groups.drop (a.1 + 1) := by
            rw [hap]
            have hdrop_a' := hdrop_a
            dsimp [suffixBlocks] at hdrop_a'
            exact hdrop_a'
          simp [h1, h2]
        have this' :
            (groups.get p :: groups.get a :: groups.drop (a.1 + 1)).IsChain
              (fun g₁ g₂ : Bool × List ℤ => g₁.1 ≠ g₂.1) := by
          simpa [hshape] using this
        exact (List.isChain_cons_cons.1 this').1

      have hside_prev : side lastPrev = (groups.get p).1 := by
        have hp_mem : groups.get p ∈ groupBySide side u := by simp [groups]
        have : lastPrev ∈ (groups.get p).2 := by
          simp [prevList, lastPrev]
        exact groupBySide_side_eq_fst side u (g := groups.get p) hp_mem lastPrev this
      have hside_curr : side headCurr = (groups.get a).1 := by
        have ha_mem : groups.get a ∈ groupBySide side u := by simp [groups]
        have : headCurr ∈ (groups.get a).2 := by
          simp [currList, headCurr]
        exact groupBySide_side_eq_fst side u (g := groups.get a) ha_mem headCurr this

      have lastPrev_mem_union : lastPrev ∈ (s ∪ t : Set ℤ) := by
        -- since `lastPrev ∈ u` and `u` is the sort of `s ∪ t`
        have : lastPrev ∈ u := by
          have : lastPrev ∈ groups.flatMap (fun g => g.2) := by
            have hp_mem : groups.get p ∈ groups := List.get_mem groups p
            exact List.mem_flatMap.2 ⟨groups.get p, hp_mem, by simp [prevList, lastPrev]⟩
          simpa [hu] using this
        have : lastPrev ∈ (s ∪ t) := (Finset.mem_sort (r := (· ≤ ·)) (s := s ∪ t) (a := lastPrev)).1 (by simpa [u] using this)
        simpa using this
      have headCurr_mem_union : headCurr ∈ (s ∪ t : Set ℤ) := by
        have : headCurr ∈ u := by
          have : headCurr ∈ groups.flatMap (fun g => g.2) := by
            have ha_mem : groups.get a ∈ groups := List.get_mem groups a
            exact List.mem_flatMap.2 ⟨groups.get a, ha_mem, by simp [currList, headCurr]⟩
          simpa [hu] using this
        have : headCurr ∈ (s ∪ t) := (Finset.mem_sort (r := (· ≤ ·)) (s := s ∪ t) (a := headCurr)).1 (by simpa [u] using this)
        simpa using this

      have hnatAbs : Int.natAbs (lastPrev - headCurr) > k := by
        -- case split on which side the previous block is on
        by_cases hprevBool : (groups.get p).1 = true
        · -- `lastPrev ∈ s`, `headCurr ∈ t`
          have hlastS : lastPrev ∈ (s : Set ℤ) := by
            have : side lastPrev = true := hside_prev.trans hprevBool
            -- `side` is `decide (∈ s)`
            exact (decide_eq_true_eq.mp (by simpa [side] using this))
          have hheadNotS : headCurr ∉ (s : Set ℤ) := by
            -- bools differ, so current is `false`
            have hnot : ¬(groups.get a).1 = true := by
              intro hc
              apply hfst_ne
              exact hprevBool.trans hc.symm
            have hcurrBool : (groups.get a).1 = false := Bool.eq_false_of_not_eq_true hnot
            have hsideFalse : side headCurr = false := hside_curr.trans hcurrBool
            intro hs'
            have hsFin : headCurr ∈ s := by simpa using hs'
            have hsideTrue : side headCurr = true := by
              have : decide (headCurr ∈ s) = true := by
                simpa using (decide_eq_true_eq.mpr hsFin)
              simpa [side] using this
            have : false = true := hsideFalse.symm.trans hsideTrue
            cases this
          have hheadT : headCurr ∈ (t : Set ℤ) := by
            have : headCurr ∈ (s : Set ℤ) ∪ (t : Set ℤ) := by simpa [Set.mem_union] using headCurr_mem_union
            rcases this with hs' | ht'
            · exact (hheadNotS hs').elim
            · exact ht'
          exact hst (a := lastPrev) hlastS (b := headCurr) hheadT
        · -- `lastPrev ∈ t`, `headCurr ∈ s` and use symmetry
          have hprevBool' : (groups.get p).1 = false :=
            Bool.eq_false_of_not_eq_true hprevBool
          have hcurrBool : (groups.get a).1 = true := by
            apply Bool.eq_true_of_not_eq_false
            intro hc
            apply hfst_ne
            exact hprevBool'.trans hc.symm
          have hlastNotS : lastPrev ∉ (s : Set ℤ) := by
            have hsideFalse : side lastPrev = false := hside_prev.trans hprevBool'
            intro hs'
            have hsFin : lastPrev ∈ s := by simpa using hs'
            have hsideTrue : side lastPrev = true := by
              have : decide (lastPrev ∈ s) = true := by
                simpa using (decide_eq_true_eq.mpr hsFin)
              simpa [side] using this
            have : false = true := hsideFalse.symm.trans hsideTrue
            cases this
          have hlastT : lastPrev ∈ (t : Set ℤ) := by
            have : lastPrev ∈ (s : Set ℤ) ∪ (t : Set ℤ) := by simpa [Set.mem_union] using lastPrev_mem_union
            rcases this with hs' | ht'
            · exact (hlastNotS hs').elim
            · exact ht'
          have hheadS : headCurr ∈ (s : Set ℤ) := by
            have : side headCurr = true := hside_curr.trans hcurrBool
            exact (decide_eq_true_eq.mp (by simpa [side] using this))
          have hst' : IndexSeparated (t : Set ℤ) (s : Set ℤ) k :=
            IndexSeparated.symm (A := (s : Set ℤ)) (B := (t : Set ℤ)) hst
          exact hst' (a := lastPrev) hlastT (b := headCurr) hheadS

      -- A useful bound: `cut + k ≤ headCurr`.
      have hcutk_le_head : cut + k ≤ headCurr := by
        have hklt : lastPrev + (k : ℤ) < headCurr := add_lt_of_natAbs_sub_gt hlt hnatAbs
        have hkle : lastPrev + (k : ℤ) + 1 ≤ headCurr := Int.add_one_le_of_lt hklt
        simpa [cut, add_assoc, add_left_comm, add_comm] using hkle

      -- The current block lies in the future half-line.
      have hblock_a_le_future : m a ≤ futureMeasurableSpace (q := q) cut k := by
        have htail : (currList ++ (groups.drop (a.1 + 1)).flatMap (fun g => g.2)).IsChain (fun a b : ℤ => a < b) := by
          -- `suffixList` is this append, and it is a chain.
          simpa [hsuffixList] using hchain_suffix
        have hchain_curr : currList.IsChain (fun a b : ℤ => a < b) :=
          (by simpa using htail.left_of_append)
        have : blockSet a ⊆ {j : ℤ | cut + k ≤ j} := by
          intro z hz
          have hz_curr : z ∈ currList := by simpa [blockSet, currList] using hz
          -- `headCurr ≤ z`
          have hhead_le : headCurr ≤ z := by
            cases hcurr : currList with
            | nil =>
                cases hcurr_ne hcurr
            | cons x xs =>
                have hz' : z = x ∨ z ∈ xs := by simpa [hcurr] using hz_curr
                rcases hz' with rfl | hzxs
                · simp [headCurr, hcurr]
                · have hxz : x < z := by
                    have hchain' : (x :: xs).IsChain (fun a b : ℤ => a < b) := by
                      simpa [hcurr] using hchain_curr
                    exact
                      hchain'.rel_cons (R := fun a b : ℤ => a < b) (a := x) (b := z) hzxs
                  have : headCurr < z := by
                    simpa [headCurr, hcurr] using hxz
                  exact le_of_lt this
          exact le_trans hcutk_le_head hhead_le
        exact coordMeasurableSpace_mono (q := q) this

      -- The σ-algebra generated by previous blocks lies in the past half-line.
      have hprev_le_past : (⨆ b : {b : Fin n // b < a}, m b.1) ≤ pastMeasurableSpace (q := q) cut := by
        refine iSup_le ?_
        rintro ⟨b, hb⟩
        have : blockSet b ⊆ {j : ℤ | j < cut} := by
          intro z hz
          -- membership in the prefix list
          have hbNat : b.1 < a.1 := hb
          have hb_mem : groups.get b ∈ prefixBlocks := by
            -- `groups.get b` is among the first `a.1` blocks
            have hb_len : b.1 < prefixBlocks.length := by
              have ha_le : a.1 ≤ groups.length := Nat.le_of_lt a.2
              simpa [prefixBlocks, List.length_take, Nat.min_eq_left ha_le] using hbNat
            -- `prefixBlocks[b] = groups[b] = groups.get b`
            have h_eq : (prefixBlocks : List (Bool × List ℤ))[b.1] = groups.get b := by
              have h1 : groups[b.1] = (prefixBlocks : List (Bool × List ℤ))[b.1] :=
                List.getElem_take' (xs := groups) (i := b.1) (j := a.1) (hi := b.2) (hj := hbNat)
              have h2 : (prefixBlocks : List (Bool × List ℤ))[b.1] = groups[b.1] := h1.symm
              have h3 : groups[b.1] = groups.get b := by
                simp
              exact h2.trans h3
            have hmem : (prefixBlocks : List (Bool × List ℤ))[b.1] ∈ prefixBlocks := List.getElem_mem hb_len
            exact h_eq ▸ hmem
          have hz_block : z ∈ (groups.get b).2 := by simpa [blockSet] using hz
          have hz_prefix : z ∈ prefixList := List.mem_flatMap.2 ⟨groups.get b, hb_mem, hz_block⟩
          -- any element in the prefix is ≤ the last one
          have hz_le : z ≤ prefixList.getLast (List.ne_nil_of_mem hz_prefix) :=
            le_getLast_of_mem_of_isChain_lt (l := prefixList) hchain_prefix hz_prefix
          -- `prefixList.getLast = lastPrev`
          have hlast : prefixList.getLast (List.ne_nil_of_mem hz_prefix) = lastPrev := by
            -- use the explicit append form of the prefix and `getLast_congr` to change proofs
            have hprefixEq : prefixList = (groups.take pNat).flatMap (fun g => g.2) ++ prevList := hprefixList
            have happendNe : ((groups.take pNat).flatMap (fun g => g.2) ++ prevList) ≠ [] :=
              List.append_ne_nil_of_right_ne_nil _ hprev_ne
            have hcongr :
                prefixList.getLast (List.ne_nil_of_mem hz_prefix) =
                  ((groups.take pNat).flatMap (fun g => g.2) ++ prevList).getLast happendNe :=
              List.getLast_congr (List.ne_nil_of_mem hz_prefix) happendNe hprefixEq
            have happ :
                ((groups.take pNat).flatMap (fun g => g.2) ++ prevList).getLast happendNe =
                  prevList.getLast hprev_ne :=
              List.getLast_append_of_right_ne_nil _ _ hprev_ne
            simpa [lastPrev, prevList] using hcongr.trans (happ.trans rfl)
          have hz_le' : z ≤ lastPrev := by simpa [hlast] using hz_le
          exact Int.lt_add_one_of_le (by simpa [cut] using hz_le')
        exact coordMeasurableSpace_mono (q := q) this

      -- Apply cut independence and restrict to the relevant σ-algebras.
      have hind_cut :
          Indep (pastMeasurableSpace (q := q) cut) (futureMeasurableSpace (q := q) cut k)
            (μ := (μ : Measure (ℤ → Fin q))) := hcut cut
      have hind1 :
          Indep (pastMeasurableSpace (q := q) cut) (m a) (μ := (μ : Measure (ℤ → Fin q))) :=
        ProbabilityTheory.indep_of_indep_of_le_right hind_cut hblock_a_le_future
      have hind2 :
          Indep (m a) (pastMeasurableSpace (q := q) cut) (μ := (μ : Measure (ℤ → Fin q))) := hind1.symm
      exact ProbabilityTheory.indep_of_indep_of_le_right hind2 hprev_le_past

  have hST : Disjoint Strue Sfalse := by
    refine Set.disjoint_left.2 ?_
    intro i hiT hiF
    have : true = false := hiT.symm.trans hiF
    cases this

  have hind_blocks :
      Indep (⨆ i ∈ Strue, m i) (⨆ i ∈ Sfalse, m i) (μ := (μ : Measure (ℤ → Fin q))) := by
    have h_le : ∀ i : Fin n, m i ≤ (MeasurableSpace.pi : MeasurableSpace (ℤ → Fin q)) := by
      intro i
      exact coordMeasurableSpace_le_pi (q := q) (blockSet i)
    exact ProbabilityTheory.indep_iSup_of_disjoint (m := m) (μ := (μ : Measure (ℤ → Fin q))) h_le hm_iIndep hST

  -- `coordMeasurableSpace s` is contained in the supremum of the `true` blocks.
  have hcoord_s_le : coordMeasurableSpace (q := q) (s : Set ℤ) ≤ ⨆ i ∈ Strue, m i := by
    refine iSup_le ?_
    rintro ⟨j, hj⟩
    have hj_union : j ∈ (s ∪ t) := Finset.mem_union.2 (Or.inl hj)
    have hj_u : j ∈ u := by
      simpa [u] using (Finset.mem_sort (r := (· ≤ ·)) (s := s ∪ t) (a := j)).2 hj_union
    have hj_flat : j ∈ groups.flatMap (fun g => g.2) := by simpa [hu] using hj_u
    rcases List.mem_flatMap.1 hj_flat with ⟨g, hg_groups, hjg⟩
    rcases List.mem_iff_get.1 hg_groups with ⟨i, rfl⟩
    have hiT : i ∈ Strue := by
      have hmem : groups.get i ∈ groupBySide side u := by simp [groups]
      have hside : side j = (groups.get i).1 :=
        groupBySide_side_eq_fst side u (g := groups.get i) hmem j hjg
      have : side j = true := by
        -- `side` is `decide (∈ s)`
        have : decide (j ∈ s) = true := by simpa using (decide_eq_true_eq.mpr hj)
        simpa [side] using this
      simpa [Strue, this] using hside.symm
    have hj_block : j ∈ blockSet i := by simpa [blockSet] using hjg
    have hcomap_le : MeasurableSpace.comap (fun x : ℤ → Fin q => x j) inferInstance ≤ m i := by
      exact le_iSup (fun j : {j : ℤ // j ∈ blockSet i} =>
        MeasurableSpace.comap (fun x : ℤ → Fin q => x j.1) inferInstance) ⟨j, hj_block⟩
    have hmi_le : m i ≤ ⨆ i ∈ Strue, m i := by
      refine le_trans ?_ (le_iSup (fun i : Fin n => ⨆ (_ : i ∈ Strue), m i) i)
      exact le_iSup (fun _ : i ∈ Strue => m i) hiT
    exact le_trans hcomap_le hmi_le

  -- Similarly for `t` and the `false` blocks.
  have hcoord_t_le : coordMeasurableSpace (q := q) (t : Set ℤ) ≤ ⨆ i ∈ Sfalse, m i := by
    refine iSup_le ?_
    rintro ⟨j, hj⟩
    have hj_union : j ∈ (s ∪ t) := Finset.mem_union.2 (Or.inr hj)
    have hj_u : j ∈ u := by
      simpa [u] using (Finset.mem_sort (r := (· ≤ ·)) (s := s ∪ t) (a := j)).2 hj_union
    have hj_flat : j ∈ groups.flatMap (fun g => g.2) := by simpa [hu] using hj_u
    rcases List.mem_flatMap.1 hj_flat with ⟨g, hg_groups, hjg⟩
    rcases List.mem_iff_get.1 hg_groups with ⟨i, rfl⟩
    have hiF : i ∈ Sfalse := by
      have hmem : groups.get i ∈ groupBySide side u := by simp [groups]
      have hside : side j = (groups.get i).1 :=
        groupBySide_side_eq_fst side u (g := groups.get i) hmem j hjg
      have hj_not_s : j ∉ (s : Set ℤ) := by
        intro hs'
        exact (Set.disjoint_left.1 hdisj hs' hj)
      have : side j = false := by
        have : decide (j ∈ s) = false := decide_eq_false hj_not_s
        simpa [side] using this
      simpa [Sfalse, this] using hside.symm
    have hj_block : j ∈ blockSet i := by simpa [blockSet] using hjg
    have hcomap_le : MeasurableSpace.comap (fun x : ℤ → Fin q => x j) inferInstance ≤ m i := by
      exact le_iSup (fun j : {j : ℤ // j ∈ blockSet i} =>
        MeasurableSpace.comap (fun x : ℤ → Fin q => x j.1) inferInstance) ⟨j, hj_block⟩
    have hmi_le : m i ≤ ⨆ i ∈ Sfalse, m i := by
      refine le_trans ?_ (le_iSup (fun i : Fin n => ⨆ (_ : i ∈ Sfalse), m i) i)
      exact le_iSup (fun _ : i ∈ Sfalse => m i) hiF
    exact le_trans hcomap_le hmi_le

  exact
    ProbabilityTheory.indep_of_indep_of_le_left
      (ProbabilityTheory.indep_of_indep_of_le_right hind_blocks hcoord_t_le)
      hcoord_s_le

/-! ### Cut ⇒ noncontiguous for arbitrary index sets -/

private lemma coordMeasurableSpace_eq_iSup_finset_subtype (A : Set ℤ) :
    coordMeasurableSpace (q := q) A =
      ⨆ s : {s : Finset ℤ // (s : Set ℤ) ⊆ A}, coordMeasurableSpace (q := q) (s.1 : Set ℤ) := by
  classical
  refine le_antisymm ?_ ?_
  · -- Each coordinate belongs to a singleton finset contained in `A`.
    refine iSup_le ?_
    rintro ⟨j, hjA⟩
    let s : Finset ℤ := {j}
    have hsA : (s : Set ℤ) ⊆ A := by
      intro x hx
      have hxFin : x ∈ s := by simpa using hx
      have hxEq : x = j := by simpa [s] using (Finset.mem_singleton.1 hxFin)
      simpa [hxEq] using hjA
    have hjS : j ∈ (s : Set ℤ) := by simp [s]
    have hcomap_le :
        MeasurableSpace.comap (fun x : ℤ → Fin q => x j) inferInstance ≤
          coordMeasurableSpace (q := q) (s : Set ℤ) := by
      exact le_iSup (fun j : {j : ℤ // j ∈ (s : Set ℤ)} =>
        MeasurableSpace.comap (fun x : ℤ → Fin q => x j.1) inferInstance) ⟨j, hjS⟩
    have hs_le :
        coordMeasurableSpace (q := q) (s : Set ℤ) ≤
          ⨆ t : {t : Finset ℤ // (t : Set ℤ) ⊆ A}, coordMeasurableSpace (q := q) (t.1 : Set ℤ) :=
      le_iSup (fun t : {t : Finset ℤ // (t : Set ℤ) ⊆ A} =>
        coordMeasurableSpace (q := q) (t.1 : Set ℤ)) ⟨s, hsA⟩
    exact le_trans hcomap_le hs_le
  · -- Every finite subset's σ-algebra is contained in `coordMeasurableSpace A`.
    refine iSup_le ?_
    intro s
    exact coordMeasurableSpace_mono (q := q) (A := (s.1 : Set ℤ)) (B := A) s.2

private lemma directed_coordMeasurableSpace_finset_subtype (A : Set ℤ) :
    Directed (· ≤ ·) (fun s : {s : Finset ℤ // (s : Set ℤ) ⊆ A} =>
      coordMeasurableSpace (q := q) (s.1 : Set ℤ)) := by
  classical
  intro s₁ s₂
  refine ⟨⟨s₁.1 ∪ s₂.1, ?_⟩, ?_, ?_⟩
  · intro x hx
    have hxFin : x ∈ s₁.1 ∪ s₂.1 := by simpa using hx
    rcases (Finset.mem_union.1 hxFin) with hx₁ | hx₂
    · exact s₁.2 (by simpa using hx₁)
    · exact s₂.2 (by simpa using hx₂)
  · -- `s₁ ⊆ s₁ ∪ s₂`
    refine coordMeasurableSpace_mono (q := q) ?_
    intro x hx
    have hxFin : x ∈ s₁.1 := by simpa using hx
    have : x ∈ s₁.1 ∪ s₂.1 := (Finset.mem_union.2 (Or.inl hxFin))
    simpa using this
  · -- `s₂ ⊆ s₁ ∪ s₂`
    refine coordMeasurableSpace_mono (q := q) ?_
    intro x hx
    have hxFin : x ∈ s₂.1 := by simpa using hx
    have : x ∈ s₁.1 ∪ s₂.1 := (Finset.mem_union.2 (Or.inr hxFin))
    simpa using this

theorem isKDependentNoncontig_of_isKDependent {μ : ProbabilityMeasure (ℤ → Fin q)} {k : ℕ}
    (hcut : IsKDependent (q := q) μ k) : IsKDependentNoncontig (q := q) μ k := by
  classical
  haveI : MeasureTheory.IsProbabilityMeasure (μ := (μ : Measure (ℤ → Fin q))) := inferInstance
  haveI : MeasureTheory.IsZeroOrProbabilityMeasure (μ := (μ : Measure (ℤ → Fin q))) := inferInstance
  intro A B hAB
  -- Approximate both index sets by directed families of finite subsets.
  let ιA : Type := {s : Finset ℤ // (s : Set ℤ) ⊆ A}
  let ιB : Type := {t : Finset ℤ // (t : Set ℤ) ⊆ B}
  let mA : ιA → MeasurableSpace (ℤ → Fin q) := fun s => coordMeasurableSpace (q := q) (s.1 : Set ℤ)
  let mB : ιB → MeasurableSpace (ℤ → Fin q) := fun t => coordMeasurableSpace (q := q) (t.1 : Set ℤ)

  have hdirA : Directed (· ≤ ·) mA := by
    simpa [mA] using directed_coordMeasurableSpace_finset_subtype (q := q) (A := A)
  have hdirB : Directed (· ≤ ·) mB := by
    simpa [mB] using directed_coordMeasurableSpace_finset_subtype (q := q) (A := B)

  have hleA : ∀ s : ιA, mA s ≤ (MeasurableSpace.pi : MeasurableSpace (ℤ → Fin q)) := by
    intro s
    simpa [mA] using coordMeasurableSpace_le_pi (q := q) (s.1 : Set ℤ)
  have hleB : ∀ t : ιB, mB t ≤ (MeasurableSpace.pi : MeasurableSpace (ℤ → Fin q)) := by
    intro t
    simpa [mB] using coordMeasurableSpace_le_pi (q := q) (t.1 : Set ℤ)

  have hindA : ∀ t : ιB,
      Indep (⨆ s : ιA, mA s) (mB t) (μ := (μ : Measure (ℤ → Fin q))) := by
    intro t
    refine ProbabilityTheory.indep_iSup_of_directed_le (μ := (μ : Measure (ℤ → Fin q)))
      (m := mA) (m1 := mB t) (_mΩ := (MeasurableSpace.pi : MeasurableSpace (ℤ → Fin q)))
      ?_ hleA (hleB t) hdirA
    intro s
    have hsepA : IndexSeparated (A := (s.1 : Set ℤ)) (B := B) k :=
      IndexSeparated.subset_left (A := A) (B := B) (A' := (s.1 : Set ℤ)) (k := k) hAB s.2
    have hsep : IndexSeparated (A := (s.1 : Set ℤ)) (B := (t.1 : Set ℤ)) k :=
      IndexSeparated.subset_right (A := (s.1 : Set ℤ)) (B := B) (B' := (t.1 : Set ℤ)) (k := k) hsepA t.2
    simpa [mA, mB] using
      indep_coordMeasurableSpace_finset_of_isKDependent (q := q) (μ := μ) (k := k) hcut (s := s.1) (t := t.1) hsep

  have hind :
      Indep (⨆ s : ιA, mA s) (⨆ t : ιB, mB t) (μ := (μ : Measure (ℤ → Fin q))) := by
    have hind' : Indep (⨆ t : ιB, mB t) (⨆ s : ιA, mA s) (μ := (μ : Measure (ℤ → Fin q))) := by
      refine ProbabilityTheory.indep_iSup_of_directed_le (μ := (μ : Measure (ℤ → Fin q)))
        (m := mB) (m1 := ⨆ s : ιA, mA s) (_mΩ := (MeasurableSpace.pi : MeasurableSpace (ℤ → Fin q)))
        ?_ hleB ?_ hdirB
      · intro t
        exact (hindA t).symm
      · -- `m1 ≤ pi`
        refine iSup_le ?_
        intro s
        exact hleA s
    exact hind'.symm

  have hEqA :
      coordMeasurableSpace (q := q) A =
        ⨆ s : ιA, mA s := by
    simpa [ιA, mA] using coordMeasurableSpace_eq_iSup_finset_subtype (q := q) (A := A)
  have hEqB :
      coordMeasurableSpace (q := q) B =
        ⨆ t : ιB, mB t := by
    simpa [ιB, mB] using coordMeasurableSpace_eq_iSup_finset_subtype (q := q) (A := B)

  -- Rewrite the goal’s σ-algebras into directed `iSup`s over finite subsets.
  have hEqA' :
      FiniteDependence.coordMeasurableSpace (coord := fun x : ℤ → Fin q => x) A =
        ⨆ s : ιA, mA s := by
    simpa [FiniteDependence.Coloring.coordMeasurableSpace] using hEqA
  have hEqB' :
      FiniteDependence.coordMeasurableSpace (coord := fun x : ℤ → Fin q => x) B =
        ⨆ t : ιB, mB t := by
    simpa [FiniteDependence.Coloring.coordMeasurableSpace] using hEqB

  simpa [hEqA', hEqB'] using hind

end CutToNoncontig

/-- For processes indexed by `ℤ`, the Holroyd–Liggett “cut” definition of `k`-dependence
(`IsKDependent`) is equivalent to the usual formulation: independence of the σ-algebras generated
by any two `k`-separated (possibly interlaced) index sets (`IsKDependentNoncontig`). -/
theorem isKDependent_iff_isKDependentNoncontig {μ : ProbabilityMeasure (ℤ → Fin q)} {k : ℕ} :
    IsKDependent (q := q) μ k ↔ IsKDependentNoncontig (q := q) μ k := by
  constructor
  · exact isKDependentNoncontig_of_isKDependent (q := q)
  · exact isKDependent_of_isKDependentNoncontig (q := q)

end DependenceEquivalence

end FiniteDependence.Coloring
