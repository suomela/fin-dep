import FiniteDependence.Coloring.Intervals
import FiniteDependence.Coloring.Distributions
import Mathlib.MeasureTheory.Measure.ProbabilityMeasure

/-!
# Constructing the `q = 3` cylinder measures on integer intervals

This file defines the finite-dimensional distributions on the intervals `[a, a+n)` as measures on
functions `IcoIdx a n → Fin 3`, obtained by transporting the `PMF` `Word.pmf3 n` along the
equivalence `Fin n ≃ IcoIdx a n`.

We prove the two consistency lemmas obtained by dropping the rightmost or leftmost coordinate.
-/

open scoped ENNReal BigOperators

namespace FiniteDependence.Coloring

namespace Word

open MeasureTheory

/-- The `P3`-law on the integer interval `[a, a+n)`. -/
noncomputable def intervalMeasure3 (a : ℤ) (n : ℕ) : Measure (IcoIdx a n → Fin 3) :=
  Measure.map (wordToIco (q := 3) a n) (pmf3 n).toMeasure

/-! ## Shifting the interval index -/

/-- The index-shift map `i ↦ i+1` from `[a, a+n)` to `[a+1, a+1+n)`. -/
noncomputable def shiftIcoIdx3 (a : ℤ) (n : ℕ) : IcoIdx a n → IcoIdx (a + 1) n :=
  fun i =>
    ⟨i.1 + 1, by
      have hi : a ≤ i.1 ∧ i.1 < a + (n : ℤ) := by
        simpa [IcoIdx] using (Finset.mem_Ico).1 i.2
      refine (Finset.mem_Ico).2 ?_
      constructor
      · linarith
      · -- `i.1 + 1 < a + 1 + n`
        have : i.1 + 1 < a + (n : ℤ) + 1 := by linarith
        simpa [add_assoc, add_left_comm, add_comm] using this⟩

/-- Precompose an assignment on `[a+1, a+1+n)` with the shift map from `[a, a+n)`. -/
noncomputable def precompShiftIcoIdx3 (a : ℤ) (n : ℕ) :
    (IcoIdx (a + 1) n → Fin 3) → (IcoIdx a n → Fin 3) :=
  fun f i => f (shiftIcoIdx3 a n i)

lemma precompShiftIcoIdx3_wordToIco (a : ℤ) (n : ℕ) (w : Word 3 n) :
    precompShiftIcoIdx3 a n (wordToIco (q := 3) (a + 1) n w) = wordToIco (q := 3) a n w := by
  classical
  funext i
  -- It suffices to identify the corresponding `Fin n` index under `equivIco`.
  have hsymm :
      (equivIco (a + 1) n).symm (shiftIcoIdx3 a n i) = (equivIco a n).symm i := by
    -- Compute by applying `equivIco (a+1) n` to both sides.
    apply (equivIco (a + 1) n).injective
    -- RHS
    have hR : (equivIco (a + 1) n) ((equivIco a n).symm i) = shiftIcoIdx3 a n i := by
      cases n with
      | zero =>
          -- The interval `[a, a+0)` is empty.
          exact (isEmptyElim i)
      | succ n =>
          -- Use the concrete description of `equivIco` for `n+1`.
          -- Let `k` be the coordinate of `i` in `Fin (n+1)`.
          set k : Fin (n + 1) := (equivIco a (n + 1)).symm i with hk
          -- From `apply_symm_apply`, recover the underlying integer of `i`.
          have hk_val : i.1 = a + (k.1 : ℤ) := by
            have : (equivIco a (n + 1)) k = i := by
              simp [hk]
            have := congrArg (fun t : ↥(IcoIdx a (n + 1)) => (t : ℤ)) this
            -- `equivIco` sends `k` to `a + k`.
            simpa [equivIco, IcoIdx] using this.symm
          -- Now compare underlying integers.
          apply Subtype.ext
          -- RHS value is `i.1 + 1`.
          -- LHS value is `(a+1) + k`.
          -- Use `hk_val : i.1 = a + k` to conclude.
          have : (i.1 : ℤ) + 1 = (a + 1) + (k.1 : ℤ) := by
            -- `i.1 + 1 = (a + k) + 1 = (a+1) + k`.
            calc
              i.1 + 1 = (a + (k.1 : ℤ)) + 1 := by simp [hk_val]
              _ = (a + 1) + (k.1 : ℤ) := by abel
          simp [shiftIcoIdx3, hk, equivIco, IcoIdx, this]
    -- Finish.
    simpa using hR.symm
  simp [precompShiftIcoIdx3, wordToIco, hsymm]

lemma precompShiftIcoIdx3_comp_wordToIco (a : ℤ) (n : ℕ) :
    precompShiftIcoIdx3 a n ∘ wordToIco (q := 3) (a + 1) n = wordToIco (q := 3) a n := by
  funext w
  simpa using precompShiftIcoIdx3_wordToIco (a := a) (n := n) w

lemma intervalMeasure3_map_precompShiftIcoIdx3 (a : ℤ) (n : ℕ) :
    (intervalMeasure3 (a + 1) n).map (precompShiftIcoIdx3 a n) = intervalMeasure3 a n := by
  classical
  have hmeas_word : Measurable (wordToIco (q := 3) (a + 1) n) := by
    simpa using (measurable_of_finite (wordToIco (q := 3) (a + 1) n))
  have hmeas_pre : Measurable (precompShiftIcoIdx3 a n) := by
    simpa using (measurable_of_finite (precompShiftIcoIdx3 a n))
  -- `intervalMeasure3` is the pushforward of `pmf3 n` along `wordToIco`; shifting the interval
  -- corresponds to precomposing with the index shift.
  simp [intervalMeasure3, Measure.map_map hmeas_pre hmeas_word, precompShiftIcoIdx3_comp_wordToIco]

lemma intervalMeasure3_singleton (a : ℤ) (n : ℕ) (f : IcoIdx a n → Fin 3) :
    intervalMeasure3 a n {f} = P3 n (icoToWord (q := 3) a n f) := by
  classical
  have hmeas : Measurable (wordToIco (q := 3) a n) := by
    simpa using (measurable_of_finite (wordToIco (q := 3) a n))
  have hpre :
      (wordToIco (q := 3) a n) ⁻¹' ({f} : Set (IcoIdx a n → Fin 3)) = {icoToWord (q := 3) a n f} := by
    ext w
    constructor
    · intro hw
      have hw' : wordToIco (q := 3) a n w = f := by
        simpa [Set.mem_preimage, Set.mem_singleton_iff] using hw
      have : icoToWord (q := 3) a n (wordToIco (q := 3) a n w) = icoToWord (q := 3) a n f := by
        simp [hw']
      simpa [icoToWord_wordToIco (q := 3) a n w] using this
    · intro hw
      have hw' : w = icoToWord (q := 3) a n f := by
        simpa [Set.mem_singleton_iff] using hw
      subst hw'
      simp [Set.mem_preimage, Set.mem_singleton_iff, wordToIco_icoToWord]
  have hs : MeasurableSet ({f} : Set (IcoIdx a n → Fin 3)) := measurableSet_singleton f
  simp [intervalMeasure3, Measure.map_apply hmeas hs, hpre, pmf3]
  rfl

/-- Restricting `[a, a+(n+1))` to `[a, a+n)` marginalizes the last coordinate. -/
lemma intervalMeasure3_map_restrict_snoc (a : ℤ) (n : ℕ) :
    (intervalMeasure3 a (n + 1)).map
        (Finset.restrict₂ (π := fun _ : ℤ => Fin 3) (Ico_subset_Ico_succ a n))
      = intervalMeasure3 a n := by
  classical
  refine Measure.ext_of_singleton (α := (IcoIdx a n → Fin 3)) ?_
  intro f
  have hmeas_restrict :
      Measurable (Finset.restrict₂ (π := fun _ : ℤ => Fin 3) (Ico_subset_Ico_succ a n)) :=
    Finset.measurable_restrict₂ (X := fun _ : ℤ => Fin 3) (Ico_subset_Ico_succ a n)
  have hs : MeasurableSet ({f} : Set (IcoIdx a n → Fin 3)) := measurableSet_singleton f
  rw [Measure.map_apply hmeas_restrict hs]

  have hmeas_word : Measurable (wordToIco (q := 3) a (n + 1)) := by
    simpa using (measurable_of_finite (wordToIco (q := 3) a (n + 1)))
  have hs_pre : MeasurableSet
      ((Finset.restrict₂ (π := fun _ : ℤ => Fin 3) (Ico_subset_Ico_succ a n)) ⁻¹' ({f} : Set _)) :=
    hmeas_restrict hs
  rw [intervalMeasure3, Measure.map_apply hmeas_word hs_pre]

  let x : Word 3 n := icoToWord (q := 3) a n f
  have hset :
      (wordToIco (q := 3) a (n + 1)) ⁻¹'
          ((Finset.restrict₂ (π := fun _ : ℤ => Fin 3) (Ico_subset_Ico_succ a n)) ⁻¹' ({f} : Set _))
        = {w : Word 3 (n + 1) | initWord (q := 3) (n := n) w = x} := by
    ext w
    constructor
    · intro hw
      have hw' :
          (Finset.restrict₂ (π := fun _ : ℤ => Fin 3) (Ico_subset_Ico_succ a n))
              (wordToIco (q := 3) a (n + 1) w) = f := by
        simpa [Set.mem_preimage, Set.mem_singleton_iff] using hw
      have :
          icoToWord (q := 3) a n
              ((Finset.restrict₂ (π := fun _ : ℤ => Fin 3) (Ico_subset_Ico_succ a n))
                (wordToIco (q := 3) a (n + 1) w)) = x := by
        simp [x, hw']
      simpa [x, icoToWord_restrict_wordToIco_init] using this
    · intro hw
      have hw' :
          icoToWord (q := 3) a n
              ((Finset.restrict₂ (π := fun _ : ℤ => Fin 3) (Ico_subset_Ico_succ a n))
                (wordToIco (q := 3) a (n + 1) w)) = x := by
        simpa [x, icoToWord_restrict_wordToIco_init] using hw
      have :
          (Finset.restrict₂ (π := fun _ : ℤ => Fin 3) (Ico_subset_Ico_succ a n))
              (wordToIco (q := 3) a (n + 1) w) = wordToIco (q := 3) a n x := by
        have :
            wordToIco (q := 3) a n
                (icoToWord (q := 3) a n
                  ((Finset.restrict₂ (π := fun _ : ℤ => Fin 3) (Ico_subset_Ico_succ a n))
                    (wordToIco (q := 3) a (n + 1) w)))
              = wordToIco (q := 3) a n x := by
          simp [hw']
        simpa [wordToIco_icoToWord] using this
      have hf : f = wordToIco (q := 3) a n x := by
        simpa [x] using (wordToIco_icoToWord (q := 3) a n f).symm
      simp [Set.mem_preimage, Set.mem_singleton_iff, hf, this]
  rw [hset]

  have hset' :
      ({w : Word 3 (n + 1) | initWord (q := 3) (n := n) w = x} : Set (Word 3 (n + 1)))
        = snocSet (q := 3) x := by
    ext w
    simpa [Set.mem_setOf_eq] using (mem_snocSet_iff (q := 3) (x := x) (w := w)).symm
  rw [hset']
  rw [PMF.toMeasure_apply_finset]

  have hinj : Set.InjOn (fun a' : Fin 3 => snoc x a') (↑(Finset.univ : Finset (Fin 3))) := by
    intro a' _ b' _ hab
    have : (snoc x a') (Fin.last n) = (snoc x b') (Fin.last n) :=
      congrArg (fun w => w (Fin.last n)) hab
    simpa using this
  have hsum_image :
      (∑ w ∈ snocSet (q := 3) x, (pmf3 (n + 1)) w)
        = ∑ a' : Fin 3, (pmf3 (n + 1)) (snoc x a') := by
    simpa [snocSet] using
      (Finset.sum_image (f := fun w : Word 3 (n + 1) => (pmf3 (n + 1)) w)
        (s := (Finset.univ : Finset (Fin 3))) (g := fun a' : Fin 3 => snoc x a') hinj)

  calc
    (∑ w ∈ snocSet (q := 3) x, (pmf3 (n + 1)) w)
        = ∑ a' : Fin 3, (pmf3 (n + 1)) (snoc x a') := hsum_image
    _ = ∑ a' : Fin 3, P3 (n + 1) (snoc x a') := by rfl
    _ = P3 n x := by simpa using (sum_P3_snoc (n := n) (x := x))
    _ = intervalMeasure3 a n {f} := by
          simpa [x] using (intervalMeasure3_singleton (a := a) (n := n) f).symm

/-- Restricting `[a, a+(n+1))` to `[a+1, a+1+n)` marginalizes the first coordinate. -/
lemma intervalMeasure3_map_restrict_cons (a : ℤ) (n : ℕ) :
    (intervalMeasure3 a (n + 1)).map
        (Finset.restrict₂ (π := fun _ : ℤ => Fin 3) (Ico_succ_subset a n))
      = intervalMeasure3 (a + 1) n := by
  classical
  refine Measure.ext_of_singleton (α := (IcoIdx (a + 1) n → Fin 3)) ?_
  intro f
  have hmeas_restrict :
      Measurable (Finset.restrict₂ (π := fun _ : ℤ => Fin 3) (Ico_succ_subset a n)) :=
    Finset.measurable_restrict₂ (X := fun _ : ℤ => Fin 3) (Ico_succ_subset a n)
  have hs : MeasurableSet ({f} : Set (IcoIdx (a + 1) n → Fin 3)) := measurableSet_singleton f
  rw [Measure.map_apply hmeas_restrict hs]

  have hmeas_word : Measurable (wordToIco (q := 3) a (n + 1)) := by
    simpa using (measurable_of_finite (wordToIco (q := 3) a (n + 1)))
  have hs_pre : MeasurableSet
      ((Finset.restrict₂ (π := fun _ : ℤ => Fin 3) (Ico_succ_subset a n)) ⁻¹' ({f} : Set _)) :=
    hmeas_restrict hs
  rw [intervalMeasure3, Measure.map_apply hmeas_word hs_pre]

  let x : Word 3 n := icoToWord (q := 3) (a + 1) n f
  have hset :
      (wordToIco (q := 3) a (n + 1)) ⁻¹'
          ((Finset.restrict₂ (π := fun _ : ℤ => Fin 3) (Ico_succ_subset a n)) ⁻¹' ({f} : Set _))
        = {w : Word 3 (n + 1) | tailWord (q := 3) (n := n) w = x} := by
    ext w
    constructor
    · intro hw
      have hw' :
          (Finset.restrict₂ (π := fun _ : ℤ => Fin 3) (Ico_succ_subset a n))
              (wordToIco (q := 3) a (n + 1) w) = f := by
        simpa [Set.mem_preimage, Set.mem_singleton_iff] using hw
      have :
          icoToWord (q := 3) (a + 1) n
              ((Finset.restrict₂ (π := fun _ : ℤ => Fin 3) (Ico_succ_subset a n))
                (wordToIco (q := 3) a (n + 1) w)) = x := by
        simp [x, hw']
      simpa [x, icoToWord_restrict_wordToIco_tail] using this
    · intro hw
      have hw' :
          icoToWord (q := 3) (a + 1) n
              ((Finset.restrict₂ (π := fun _ : ℤ => Fin 3) (Ico_succ_subset a n))
                (wordToIco (q := 3) a (n + 1) w)) = x := by
        simpa [x, icoToWord_restrict_wordToIco_tail] using hw
      have :
          (Finset.restrict₂ (π := fun _ : ℤ => Fin 3) (Ico_succ_subset a n))
              (wordToIco (q := 3) a (n + 1) w) = wordToIco (q := 3) (a + 1) n x := by
        have :
            wordToIco (q := 3) (a + 1) n
                (icoToWord (q := 3) (a + 1) n
                  ((Finset.restrict₂ (π := fun _ : ℤ => Fin 3) (Ico_succ_subset a n))
                    (wordToIco (q := 3) a (n + 1) w)))
              = wordToIco (q := 3) (a + 1) n x := by
          simp [hw']
        simpa [wordToIco_icoToWord] using this
      have hf : f = wordToIco (q := 3) (a + 1) n x := by
        simpa [x] using (wordToIco_icoToWord (q := 3) (a + 1) n f).symm
      simp [Set.mem_preimage, Set.mem_singleton_iff, hf, this]
  rw [hset]

  have hset' :
      ({w : Word 3 (n + 1) | tailWord (q := 3) (n := n) w = x} : Set (Word 3 (n + 1)))
        = consSet (q := 3) x := by
    ext w
    simpa [Set.mem_setOf_eq] using (mem_consSet_iff (q := 3) (x := x) (w := w)).symm
  rw [hset']
  rw [PMF.toMeasure_apply_finset]

  have hinj : Set.InjOn (fun a' : Fin 3 => cons a' x) (↑(Finset.univ : Finset (Fin 3))) := by
    intro a' _ b' _ hab
    have : (cons a' x) 0 = (cons b' x) 0 := congrArg (fun w => w 0) hab
    simpa [Word.cons] using this
  have hsum_image :
      (∑ w ∈ consSet (q := 3) x, (pmf3 (n + 1)) w)
        = ∑ a' : Fin 3, (pmf3 (n + 1)) (cons a' x) := by
    simpa [consSet] using
      (Finset.sum_image (f := fun w : Word 3 (n + 1) => (pmf3 (n + 1)) w)
        (s := (Finset.univ : Finset (Fin 3))) (g := fun a' : Fin 3 => cons a' x) hinj)

  calc
    (∑ w ∈ consSet (q := 3) x, (pmf3 (n + 1)) w)
        = ∑ a' : Fin 3, (pmf3 (n + 1)) (cons a' x) := hsum_image
    _ = ∑ a' : Fin 3, P3 (n + 1) (cons a' x) := by rfl
    _ = P3 n x := by simpa using (sum_P3_cons (n := n) (x := x))
    _ = intervalMeasure3 (a + 1) n {f} := by
          simpa [x] using (intervalMeasure3_singleton (a := a + 1) (n := n) f).symm

end Word

end FiniteDependence.Coloring
