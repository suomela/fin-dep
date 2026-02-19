import FiniteDependence.Coloring.PropertiesFour
import Mathlib.MeasureTheory.Measure.Prod
import Mathlib.Tactic

/-!
# 1-dependence of the `q = 4` process

This file proves that the probability measure `Word.μ4` constructed from the projective family
`Word.P4Family` is `1`-dependent, i.e. the past and future σ-algebras separated by one site are
independent.

The key input is the factorization identity from Holroyd–Liggett (arXiv:1403.2448v4), equation (10),
already formalized as `Word.sum_P4_insert1` in `FiniteDependence.Coloring/Distributions.lean`.
-/

open scoped BigOperators ENNReal

namespace FiniteDependence.Coloring

namespace Word

open MeasureTheory ProbabilityTheory Set

/-! ## Word-level block maps -/

/-- The middle index `m` inside `Fin (m+1+n)` (viewed as `Fin (m+1+n)` = `Fin ((m+1)+n)`). -/
noncomputable def midIndex (m n : ℕ) : Fin (m + 1 + n) :=
  Fin.castAdd n (Fin.last m)

/-- The left block of length `m` of a word of length `m+1+n`, skipping the middle letter. -/
noncomputable def leftPart (m n : ℕ) (w : Word 4 (m + 1 + n)) : Word 4 m :=
  fun i => w (Fin.castAdd n i.castSucc)

/-- The right block of length `n` of a word of length `m+1+n`, skipping the middle letter. -/
noncomputable def rightPart (m n : ℕ) (w : Word 4 (m + 1 + n)) : Word 4 n :=
  fun i => w (Fin.natAdd (m + 1) i)

/-- The pair map `(leftPart, rightPart)`. -/
noncomputable def parts (m n : ℕ) (w : Word 4 (m + 1 + n)) : Word 4 m × Word 4 n :=
  (leftPart m n w, rightPart m n w)

lemma insert1_midIndex (m n : ℕ) (x : Word 4 m) (a : Fin 4) (y : Word 4 n) :
    insert1 (q := 4) (m := m) (n := n) x a y (midIndex m n) = a := by
  -- `midIndex` is the last index of the `snoc` block.
  simp [midIndex, insert1, append, snoc]

lemma insert1_injective (m n : ℕ) (x : Word 4 m) (y : Word 4 n) :
    Function.Injective (fun a : Fin 4 => insert1 (q := 4) (m := m) (n := n) x a y) := by
  intro a₁ a₂ h
  -- Evaluate at the middle index.
  have :=
    congrArg (fun w : Word 4 (m + 1 + n) => w (midIndex m n)) h
  simpa [insert1_midIndex (m := m) (n := n) (x := x) (y := y)] using this

lemma leftPart_insert1 (m n : ℕ) (x : Word 4 m) (a : Fin 4) (y : Word 4 n) :
    leftPart m n (insert1 (q := 4) (m := m) (n := n) x a y) = x := by
  funext i
  simp [leftPart, insert1, append, snoc]

lemma rightPart_insert1 (m n : ℕ) (x : Word 4 m) (a : Fin 4) (y : Word 4 n) :
    rightPart m n (insert1 (q := 4) (m := m) (n := n) x a y) = y := by
  funext i
  simp [rightPart, insert1, append, snoc]

private lemma exists_insert1_of_parts_eq (m n : ℕ) (x : Word 4 m) (y : Word 4 n)
    (w : Word 4 (m + 1 + n)) (hx : leftPart m n w = x) (hy : rightPart m n w = y) :
    ∃ a : Fin 4, insert1 (q := 4) (m := m) (n := n) x a y = w := by
  classical
  refine ⟨w (midIndex m n), ?_⟩
  -- Use `Fin.append_castAdd_natAdd` to split `w` into a left and right block.
  have hw :
      Fin.append (fun i : Fin (m + 1) => w (Fin.castAdd n i))
          (fun j : Fin n => w (Fin.natAdd (m + 1) j)) = w := by
    -- `Fin.append_castAdd_natAdd` is stated for `m + n`; here `m := m+1`.
    simpa [Nat.add_assoc] using (Fin.append_castAdd_natAdd (f := w) (m := m + 1) (n := n))

  have hleft :
      (fun i : Fin (m + 1) => w (Fin.castAdd n i)) =
        snoc (q := 4) (n := m) x (w (midIndex m n)) := by
    funext i
    refine Fin.lastCases ?_ (fun j => ?_) i
    · -- The middle index.
      simp [midIndex, snoc]
    · -- The `j`-th index in the left block.
      have hxj : leftPart m n w j = x j := by
        simpa using congrArg (fun f : Word 4 m => f j) hx
      -- `snoc` agrees with `x` on the `castSucc` indices.
      calc
        w (Fin.castAdd n j.castSucc) = x j := by simpa [leftPart] using hxj
        _ = snoc (q := 4) (n := m) x (w (midIndex m n)) j.castSucc := by
              simp [snoc]

  have hright : (fun j : Fin n => w (Fin.natAdd (m + 1) j)) = y := by
    funext j
    have hyj : rightPart m n w j = y j := by
      simpa using congrArg (fun f : Word 4 n => f j) hy
    simpa [rightPart, hyj]

  -- Substitute into `hw`.
  -- `insert1 x a y = append (snoc x a) y` and `Word.append = Fin.append`.
  simpa [insert1, append, hleft, hright] using hw

lemma preimage_parts_singleton (m n : ℕ) (x : Word 4 m) (y : Word 4 n) :
    parts m n ⁻¹' ({(x, y)} : Set (Word 4 m × Word 4 n)) =
      (Finset.univ.image (fun a : Fin 4 =>
        insert1 (q := 4) (m := m) (n := n) x a y) : Set (Word 4 (m + 1 + n))) := by
  ext w
  constructor
  · intro hw
    have hx : leftPart m n w = x := by
      simpa [parts] using congrArg Prod.fst (by simpa [Set.mem_preimage, Set.mem_singleton_iff] using hw)
    have hy : rightPart m n w = y := by
      simpa [parts] using congrArg Prod.snd (by simpa [Set.mem_preimage, Set.mem_singleton_iff] using hw)
    rcases exists_insert1_of_parts_eq (m := m) (n := n) (x := x) (y := y) (w := w) hx hy with ⟨a, rfl⟩
    -- Membership in a finset image, then coerce to a set.
    have : insert1 (q := 4) (m := m) (n := n) x a y ∈
        Finset.univ.image (fun a : Fin 4 => insert1 (q := 4) (m := m) (n := n) x a y) := by
      exact Finset.mem_image.2 ⟨a, Finset.mem_univ a, rfl⟩
    exact (Finset.mem_coe).2 this
  · intro hw
    have hw' :
        w ∈ Finset.univ.image (fun a : Fin 4 =>
          insert1 (q := 4) (m := m) (n := n) x a y) :=
      (Finset.mem_coe).1 hw
    rcases Finset.mem_image.1 hw' with ⟨a, _ha, rfl⟩
    -- Compute the parts of an inserted word.
    simp [parts, leftPart_insert1, rightPart_insert1]

lemma pmf4_parts_singleton (m n : ℕ) (x : Word 4 m) (y : Word 4 n) :
    (pmf4 (m + 1 + n)).toMeasure
        (parts m n ⁻¹' ({(x, y)} : Set (Word 4 m × Word 4 n)))
      = P4 m x * P4 n y := by
  classical
  -- Rewrite the preimage as an image of the `insert1` map.
  rw [preimage_parts_singleton (m := m) (n := n) (x := x) (y := y)]
  -- Evaluate the `PMF` measure on a finset and use the injectivity of the `insert1` map.
  have hinj :
      Set.InjOn (fun a : Fin 4 => insert1 (q := 4) (m := m) (n := n) x a y)
        (↑(Finset.univ : Finset (Fin 4)) : Set (Fin 4)) := by
    intro a₁ _ha₁ a₂ _ha₂ h
    exact insert1_injective (m := m) (n := n) (x := x) (y := y) h
  calc
    (pmf4 (m + 1 + n)).toMeasure
        (Finset.univ.image (fun a : Fin 4 => insert1 (q := 4) (m := m) (n := n) x a y))
        =
        ∑ w ∈ Finset.univ.image (fun a : Fin 4 => insert1 (q := 4) (m := m) (n := n) x a y),
          (pmf4 (m + 1 + n)) w := by
          simpa using
            (PMF.toMeasure_apply_finset (p := pmf4 (m + 1 + n))
              (s := Finset.univ.image (fun a : Fin 4 =>
                insert1 (q := 4) (m := m) (n := n) x a y)))
    _ =
        ∑ a : Fin 4, (pmf4 (m + 1 + n)) (insert1 (q := 4) (m := m) (n := n) x a y) := by
          -- Replace the sum over the image by a sum over `Fin 4`.
          simpa using
            (Finset.sum_image (f := fun w : Word 4 (m + 1 + n) => (pmf4 (m + 1 + n)) w)
              (s := (Finset.univ : Finset (Fin 4)))
              (g := fun a : Fin 4 => insert1 (q := 4) (m := m) (n := n) x a y) hinj)
    _ = P4 m x * P4 n y := by
          -- Unfold `pmf4` and apply equation (10) from the paper.
          simpa [pmf4] using (sum_P4_insert1 (m := m) (n := n) (x := x) (y := y))

lemma pmf4_parts_map (m n : ℕ) :
    Measure.map (parts m n) (pmf4 (m + 1 + n)).toMeasure
      = (pmf4 m).toMeasure.prod (pmf4 n).toMeasure := by
  classical
  -- The codomain is finite, so it suffices to check equality on singletons.
  refine Measure.ext_of_singleton (α := Word 4 m × Word 4 n) ?_
  rintro ⟨x, y⟩
  have hmeas : MeasurableSet ({(x, y)} : Set (Word 4 m × Word 4 n)) := measurableSet_singleton _
  have hmeas_parts : Measurable (parts m n) := by
    simpa using measurable_of_finite (parts m n)
  -- LHS: compute via the singleton preimage lemma.
  have hL :
      Measure.map (parts m n) (pmf4 (m + 1 + n)).toMeasure ({(x, y)} : Set (Word 4 m × Word 4 n))
        = P4 m x * P4 n y := by
      -- Evaluate the pushforward on a singleton via the preimage.
      simpa [Measure.map_apply hmeas_parts hmeas] using
        (pmf4_parts_singleton (m := m) (n := n) (x := x) (y := y))
  -- RHS: product of singleton probabilities.
  have hR :
      (pmf4 m).toMeasure.prod (pmf4 n).toMeasure ({(x, y)} : Set (Word 4 m × Word 4 n))
        = P4 m x * P4 n y := by
    -- A singleton in the product is a product of singletons.
    have hxy :
        ({(x, y)} : Set (Word 4 m × Word 4 n)) =
          ({x} : Set (Word 4 m)) ×ˢ ({y} : Set (Word 4 n)) := by
      ext z
      simp
    calc
      (pmf4 m).toMeasure.prod (pmf4 n).toMeasure ({(x, y)} : Set (Word 4 m × Word 4 n))
          = (pmf4 m).toMeasure.prod (pmf4 n).toMeasure
              (({x} : Set (Word 4 m)) ×ˢ ({y} : Set (Word 4 n))) := by
              rw [hxy]
      _ = (pmf4 m).toMeasure ({x} : Set (Word 4 m)) * (pmf4 n).toMeasure ({y} : Set (Word 4 n)) := by
              simpa using
                (Measure.prod_prod (μ := (pmf4 m).toMeasure) (ν := (pmf4 n).toMeasure)
                  ({x} : Set (Word 4 m)) ({y} : Set (Word 4 n)))
      _ = (pmf4 m) x * (pmf4 n) y := by simp
      _ = P4 m x * P4 n y := by rfl
  simp [hL, hR]

theorem pmf4_indep_leftPart_rightPart (m n : ℕ) :
    (leftPart m n) ⟂ᵢ[(pmf4 (m + 1 + n)).toMeasure] (rightPart m n) := by
  classical
  let μ : Measure (Word 4 (m + 1 + n)) := (pmf4 (m + 1 + n)).toMeasure
  have hpair :
      μ.map (fun w => (leftPart m n w, rightPart m n w))
        = (pmf4 m).toMeasure.prod (pmf4 n).toMeasure := by
      simpa [μ, parts] using pmf4_parts_map (m := m) (n := n)
  have hf : AEMeasurable (leftPart m n) μ := (measurable_of_finite (leftPart m n)).aemeasurable
  have hg : AEMeasurable (rightPart m n) μ := (measurable_of_finite (rightPart m n)).aemeasurable

  -- Identify the marginals via the product measure.
  have hμL : μ.map (leftPart m n) = (pmf4 m).toMeasure := by
    have hmeas_pair : Measurable (fun w => (leftPart m n w, rightPart m n w)) := by
      simpa using measurable_of_finite (fun w : Word 4 (m + 1 + n) => (leftPart m n w, rightPart m n w))
    calc
      μ.map (leftPart m n)
          = (μ.map (fun w => (leftPart m n w, rightPart m n w))).map Prod.fst := by
              symm
              have hcomp :
                  (Prod.fst ∘ fun w => (leftPart m n w, rightPart m n w)) = leftPart m n := by
                funext w
                rfl
              simp [Measure.map_map measurable_fst hmeas_pair, hcomp]
      _ = ((pmf4 m).toMeasure.prod (pmf4 n).toMeasure).map Prod.fst := by
            simp [hpair]
      _ = (pmf4 m).toMeasure := by
            simp

  have hμR : μ.map (rightPart m n) = (pmf4 n).toMeasure := by
    have hmeas_pair : Measurable (fun w => (leftPart m n w, rightPart m n w)) := by
      simpa using measurable_of_finite (fun w : Word 4 (m + 1 + n) => (leftPart m n w, rightPart m n w))
    calc
      μ.map (rightPart m n)
          = (μ.map (fun w => (leftPart m n w, rightPart m n w))).map Prod.snd := by
              symm
              have hcomp :
                  (Prod.snd ∘ fun w => (leftPart m n w, rightPart m n w)) = rightPart m n := by
                funext w
                rfl
              simp [Measure.map_map measurable_snd hmeas_pair, hcomp]
      _ = ((pmf4 m).toMeasure.prod (pmf4 n).toMeasure).map Prod.snd := by
            simp [hpair]
      _ = (pmf4 n).toMeasure := by
            simp

  -- Apply the map characterization of `IndepFun`.
  have hpair' :
      μ.map (fun w => (leftPart m n w, rightPart m n w))
        = (μ.map (leftPart m n)).prod (μ.map (rightPart m n)) := by
      simpa [hμL, hμR] using hpair

  -- `μ` is finite (in fact, a probability measure).
  haveI : IsFiniteMeasure μ := by
    -- `PMF.toMeasure` is a probability measure.
    infer_instance

  exact (indepFun_iff_map_prod_eq_prod_map_map (μ := μ) hf hg).2 hpair'

/-! ## Interval and half-line independence for `μ4` -/

/-!
The rest of the file lifts the word-level independence to the two-sided process `μ4` on `ℤ`
and packages it as `IsKDependent μ4 1`.
-/

/-! ### Restriction maps on integer intervals -/

lemma equivIco_symm_val (a : ℤ) (n : ℕ) (i : IcoIdx a n) :
    ((equivIco a n).symm i).1 = (i.1 - a).toNat := by
  cases n with
  | zero =>
      exact (isEmptyElim i)
  | succ n =>
      simp [equivIco]

lemma Ico_left_subset (a : ℤ) (m n : ℕ) : IcoIdx a m ⊆ IcoIdx a (m + 1 + n) := by
  -- First include `[a, a+m)` in `[a, a+m+(n+1))`, then rewrite `m+(n+1)` as `m+1+n`.
  simpa [Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using (Ico_subset_Ico_add a m (n + 1))

lemma Ico_right_subset (a : ℤ) (m n : ℕ) : IcoIdx (a + (m + 1)) n ⊆ IcoIdx a (m + 1 + n) := by
  simpa [Nat.add_assoc] using (Ico_shift_subset (a := a) (l := m + 1) (n := n))

/-- Restrict an assignment on `[a, a+m+1+n)` to the left block `[a, a+m)`. -/
noncomputable def icoLeft (a : ℤ) (m n : ℕ) :
    (IcoIdx a (m + 1 + n) → Fin 4) → (IcoIdx a m → Fin 4) :=
  Finset.restrict₂ (π := fun _ : ℤ => Fin 4) (Ico_left_subset a m n)

/-- Restrict an assignment on `[a, a+m+1+n)` to the right block `[a+m+1, a+m+1+n)`. -/
noncomputable def icoRight (a : ℤ) (m n : ℕ) :
    (IcoIdx a (m + 1 + n) → Fin 4) → (IcoIdx (a + (m + 1)) n → Fin 4) :=
  Finset.restrict₂ (π := fun _ : ℤ => Fin 4) (Ico_right_subset a m n)

/-- The pair map of left and right restrictions. -/
noncomputable def icoParts (a : ℤ) (m n : ℕ) :
    (IcoIdx a (m + 1 + n) → Fin 4) → (IcoIdx a m → Fin 4) × (IcoIdx (a + (m + 1)) n → Fin 4) :=
  fun f => (icoLeft a m n f, icoRight a m n f)

lemma icoLeft_wordToIco (a : ℤ) (m n : ℕ) (w : Word 4 (m + 1 + n)) :
    icoLeft a m n (wordToIco (q := 4) a (m + 1 + n) w) = wordToIco (q := 4) a m (leftPart m n w) := by
  classical
  funext i
  cases m with
  | zero =>
      exact (isEmptyElim i)
  | succ m =>
      let iBig : IcoIdx a (Nat.succ m + 1 + n) := ⟨i.1, Ico_left_subset a (Nat.succ m) n i.2⟩
      have hidx :
          (equivIco a (Nat.succ m + 1 + n)).symm iBig
            = Fin.castAdd n ((equivIco a (Nat.succ m)).symm i).castSucc := by
        apply Fin.ext
        have hLval :
            ((equivIco a (Nat.succ m + 1 + n)).symm iBig).1 = (i.1 - a).toNat := by
          simpa [iBig] using equivIco_symm_val (a := a) (n := Nat.succ m + 1 + n) iBig
        have hSmall : ((equivIco a (Nat.succ m)).symm i).1 = (i.1 - a).toNat := by
          simpa using equivIco_symm_val (a := a) (n := Nat.succ m) i
        have hRval :
            (Fin.castAdd n ((equivIco a (Nat.succ m)).symm i).castSucc).1 = (i.1 - a).toNat := by
          simpa using hSmall
        exact hLval.trans hRval.symm
      simp [icoLeft, wordToIco, leftPart, iBig, hidx]

lemma toNat_sub_eq_add_toNat_sub (a b : ℤ) (m : ℕ) (h : a + m ≤ b) :
    (b - a).toNat = m + (b - (a + m)).toNat := by
  apply Int.ofNat.inj
  have hab : a ≤ b := by
    have hm0 : (0 : ℤ) ≤ (m : ℤ) := by exact_mod_cast Nat.zero_le m
    exact le_trans (le_add_of_nonneg_right hm0) h
  have hnonneg1 : 0 ≤ b - a := sub_nonneg.2 hab
  have hnonneg2 : 0 ≤ b - (a + m) := sub_nonneg.2 h
  have hz1 : ((b - a).toNat : ℤ) = b - a := Int.toNat_of_nonneg hnonneg1
  have hz2 : ((b - (a + m)).toNat : ℤ) = b - (a + m) := Int.toNat_of_nonneg hnonneg2
  calc
    ((b - a).toNat : ℤ) = b - a := hz1
    _ = (m : ℤ) + (b - (a + m)) := by abel
    _ = (m : ℤ) + ((b - (a + m)).toNat : ℤ) := by simp [hz2]
    _ = (m + (b - (a + m)).toNat : ℤ) := by
          norm_cast

lemma icoRight_wordToIco (a : ℤ) (m n : ℕ) (w : Word 4 (m + 1 + n)) :
    icoRight a m n (wordToIco (q := 4) a (m + 1 + n) w) =
      wordToIco (q := 4) (a + (m + 1)) n (rightPart m n w) := by
  classical
  funext i
  let iBig : IcoIdx a (m + 1 + n) := ⟨i.1, Ico_right_subset a m n i.2⟩
  have hidx :
      (equivIco a (m + 1 + n)).symm iBig =
        Fin.natAdd (m + 1) ((equivIco (a + (m + 1)) n).symm i) := by
    apply Fin.ext
    have hLval : ((equivIco a (m + 1 + n)).symm iBig).1 = (i.1 - a).toNat := by
      simpa [iBig] using equivIco_symm_val (a := a) (n := m + 1 + n) iBig
    have hi : a + (m + 1) ≤ i.1 := (Finset.mem_Ico).1 i.2 |>.1
    have hsplit : (i.1 - a).toNat = (m + 1) + (i.1 - (a + (m + 1))).toNat := by
      simpa [sub_eq_add_neg, add_assoc] using
        (toNat_sub_eq_add_toNat_sub (a := a) (b := i.1) (m := m + 1) hi)
    have hRbase : ((equivIco (a + (m + 1)) n).symm i).1 = (i.1 - (a + (m + 1))).toNat := by
      simpa using equivIco_symm_val (a := a + (m + 1)) (n := n) i
    have hRval :
        (Fin.natAdd (m + 1) ((equivIco (a + (m + 1)) n).symm i)).1 = (i.1 - a).toNat := by
      simp [Fin.natAdd, hRbase, hsplit]
    exact hLval.trans hRval.symm
  simp [icoRight, wordToIco, rightPart, iBig, hidx]

lemma icoParts_wordToIco (a : ℤ) (m n : ℕ) (w : Word 4 (m + 1 + n)) :
    icoParts a m n (wordToIco (q := 4) a (m + 1 + n) w)
      = (wordToIco (q := 4) a m (leftPart m n w),
        wordToIco (q := 4) (a + (m + 1)) n (rightPart m n w)) := by
  ext <;> simp [icoParts, icoLeft_wordToIco, icoRight_wordToIco]

theorem intervalMeasure4_map_icoParts (a : ℤ) (m n : ℕ) :
    Measure.map (icoParts a m n) (intervalMeasure4 a (m + 1 + n))
      = (intervalMeasure4 a m).prod (intervalMeasure4 (a + (m + 1)) n) := by
  classical
  have hmeas_word : Measurable (wordToIco (q := 4) a (m + 1 + n)) := by
    simpa using (measurable_of_finite (wordToIco (q := 4) a (m + 1 + n)))
  have hmeas_icoParts : Measurable (icoParts a m n) := by
    simpa using measurable_of_finite (icoParts a m n)
  -- Rewrite the pushforward through `wordToIco`, then apply the word-level factorization.
  calc
    Measure.map (icoParts a m n) (intervalMeasure4 a (m + 1 + n))
        = Measure.map (icoParts a m n ∘ wordToIco (q := 4) a (m + 1 + n))
            (pmf4 (m + 1 + n)).toMeasure := by
              simp [intervalMeasure4, Measure.map_map hmeas_icoParts hmeas_word]
    _ = Measure.map (fun w : Word 4 (m + 1 + n) =>
          (wordToIco (q := 4) a m (leftPart m n w),
            wordToIco (q := 4) (a + (m + 1)) n (rightPart m n w)))
          (pmf4 (m + 1 + n)).toMeasure := by
          -- pointwise identification of the composition
          refine congrArg (fun f => Measure.map f (pmf4 (m + 1 + n)).toMeasure) ?_
          funext w
          simp [Function.comp, icoParts_wordToIco (a := a) (m := m) (n := n) (w := w)]
    _ = Measure.map
          (Prod.map (wordToIco (q := 4) a m) (wordToIco (q := 4) (a + (m + 1)) n))
          (Measure.map (parts m n) (pmf4 (m + 1 + n)).toMeasure) := by
          have hmeas_parts : Measurable (parts m n) := by
            simpa using measurable_of_finite (parts m n)
          have hmeas_prod :
              Measurable
                (Prod.map (wordToIco (q := 4) a m) (wordToIco (q := 4) (a + (m + 1)) n)) := by
            simpa using measurable_of_finite
              (Prod.map (wordToIco (q := 4) a m) (wordToIco (q := 4) (a + (m + 1)) n))
          -- Express the pair map as a composition through `parts`, then apply `map_map`.
          have hfun :
              (fun w : Word 4 (m + 1 + n) =>
                  (wordToIco (q := 4) a m (leftPart m n w),
                    wordToIco (q := 4) (a + (m + 1)) n (rightPart m n w)))
                =
                (Prod.map (wordToIco (q := 4) a m) (wordToIco (q := 4) (a + (m + 1)) n)) ∘
                  parts m n := by
            funext w
            simp [Function.comp, parts]
          calc
            Measure.map (fun w : Word 4 (m + 1 + n) =>
                (wordToIco (q := 4) a m (leftPart m n w),
                  wordToIco (q := 4) (a + (m + 1)) n (rightPart m n w)))
                (pmf4 (m + 1 + n)).toMeasure
                =
                Measure.map
                  ((Prod.map (wordToIco (q := 4) a m) (wordToIco (q := 4) (a + (m + 1)) n)) ∘
                    parts m n)
                  (pmf4 (m + 1 + n)).toMeasure := by
                  simp [hfun]
            _ = Measure.map
                  (Prod.map (wordToIco (q := 4) a m) (wordToIco (q := 4) (a + (m + 1)) n))
                  (Measure.map (parts m n) (pmf4 (m + 1 + n)).toMeasure) := by
                  symm
                  simp [Measure.map_map hmeas_prod hmeas_parts]
    _ = Measure.map
          (Prod.map (wordToIco (q := 4) a m) (wordToIco (q := 4) (a + (m + 1)) n))
          ((pmf4 m).toMeasure.prod (pmf4 n).toMeasure) := by
          simp [pmf4_parts_map (m := m) (n := n)]
    _ = (intervalMeasure4 a m).prod (intervalMeasure4 (a + (m + 1)) n) := by
          -- Pushforward of the product measure factors as the product of pushforwards.
          have hmeas_left : Measurable (wordToIco (q := 4) a m) := by
            simpa using (measurable_of_finite (wordToIco (q := 4) a m))
          have hmeas_right : Measurable (wordToIco (q := 4) (a + (m + 1)) n) := by
            simpa using (measurable_of_finite (wordToIco (q := 4) (a + (m + 1)) n))
          -- `map_prod_map` is stated in the opposite direction.
          symm
          simpa [intervalMeasure4] using
            (Measure.map_prod_map (μa := (pmf4 m).toMeasure) (μc := (pmf4 n).toMeasure)
              (f := wordToIco (q := 4) a m) (g := wordToIco (q := 4) (a + (m + 1)) n)
              hmeas_left hmeas_right)

/-! ### Finite-block independence for `μ4` -/

lemma P4Family_IcoIdx (a : ℤ) : ∀ n : ℕ, P4Family (IcoIdx a n) = intervalMeasure4 a n
  | 0 => by
      classical
      refine Measure.ext_of_singleton (α := (IcoIdx a 0 → Fin 4)) ?_
      intro f
      have hf : f = (fun _ : IcoIdx a 0 => (0 : Fin 4)) := by
        funext i
        exact (isEmptyElim i)
      subst hf
      have hP : P4Family (IcoIdx a 0) = Measure.dirac (fun _ : IcoIdx a 0 => (0 : Fin 4)) := by
        simp [P4Family]
      have hsing :
          ({(fun _ : IcoIdx a 0 => (0 : Fin 4))} : Set (IcoIdx a 0 → Fin 4)) = Set.univ := by
        ext g
        have : g = (fun _ : IcoIdx a 0 => (0 : Fin 4)) := by
          funext i
          exact (isEmptyElim i)
        simp [this]
      have hleft :
          P4Family (IcoIdx a 0)
              ({(fun _ : IcoIdx a 0 => (0 : Fin 4))} : Set (IcoIdx a 0 → Fin 4))
            = 1 := by
        simp [hP]
      have hright :
          intervalMeasure4 a 0 ({(fun _ : IcoIdx a 0 => (0 : Fin 4))} : Set (IcoIdx a 0 → Fin 4))
            = 1 := by
        rw [hsing]
        have hmeas : Measurable (wordToIco (q := 4) a 0) := by
          simpa using (measurable_of_finite (wordToIco (q := 4) a 0))
        simp [intervalMeasure4, Measure.map_apply hmeas MeasurableSet.univ]
      simp [hleft, hright]
  | n + 1 => by
      simpa using (P4Family_IcoIdx_succ (a := a) (n := n))

lemma μ4Measure_map_restrict_IcoIdx (a : ℤ) (n : ℕ) :
    μ4Measure.map (IcoIdx a n).restrict = intervalMeasure4 a n := by
  -- `μ4Measure` is a projective limit with marginals `P4Family`.
  have hproj := μ4_isProjectiveLimit (I := IcoIdx a n)
  simpa [P4Family_IcoIdx (a := a) n] using hproj

lemma μ4Measure_map_restrict_pair (a : ℤ) (m n : ℕ) :
    μ4Measure.map (fun x : ℤ → Fin 4 =>
        ((IcoIdx a m).restrict x, (IcoIdx (a + (m + 1)) n).restrict x))
      = (intervalMeasure4 a m).prod (intervalMeasure4 (a + (m + 1)) n) := by
  classical
  set I : Finset ℤ := IcoIdx a (m + 1 + n) with hI
  have hmeas_restrict :
      Measurable (I.restrict : (ℤ → Fin 4) → I → Fin 4) :=
    measurable_pi_lambda _ (fun _ => measurable_pi_apply _)
  have hmeas_parts : Measurable (icoParts a m n) := by
    simpa using measurable_of_finite (icoParts a m n)
  -- Identify the pair map as a composition through `I.restrict`.
  have hcomp :
      (fun x : ℤ → Fin 4 => ((IcoIdx a m).restrict x, (IcoIdx (a + (m + 1)) n).restrict x))
        = (icoParts a m n) ∘ (I.restrict : (ℤ → Fin 4) → I → Fin 4) := by
    funext x
    ext <;> rfl
  -- Compute by mapping through the projective limit marginal on `I`.
  calc
    μ4Measure.map (fun x : ℤ → Fin 4 =>
        ((IcoIdx a m).restrict x, (IcoIdx (a + (m + 1)) n).restrict x))
        = (μ4Measure.map (I.restrict : (ℤ → Fin 4) → I → Fin 4)).map (icoParts a m n) := by
            -- `map_map` with `hcomp`.
            simp [hcomp, Measure.map_map hmeas_parts hmeas_restrict]
    _ = (P4Family I).map (icoParts a m n) := by
            -- projective limit property
            simp [μ4_isProjectiveLimit (I := I)]
    _ = (intervalMeasure4 a (m + 1 + n)).map (icoParts a m n) := by
            -- identify the marginal on the full interval
            subst I
            simp [P4Family_IcoIdx (a := a) (n := m + 1 + n)]
    _ = (intervalMeasure4 a m).prod (intervalMeasure4 (a + (m + 1)) n) := by
            simpa using (intervalMeasure4_map_icoParts (a := a) (m := m) (n := n))

theorem μ4_indep_restrict_left_right (a : ℤ) (m n : ℕ) :
    ((IcoIdx a m).restrict) ⟂ᵢ[μ4Measure] ((IcoIdx (a + (m + 1)) n).restrict) := by
  classical
  -- Use the `map` characterization of `IndepFun`.
  let f : (ℤ → Fin 4) → (IcoIdx a m → Fin 4) := (IcoIdx a m).restrict
  let g : (ℤ → Fin 4) → (IcoIdx (a + (m + 1)) n → Fin 4) := (IcoIdx (a + (m + 1)) n).restrict
  have hf : AEMeasurable f μ4Measure :=
    (Finset.measurable_restrict (X := fun _ : ℤ => Fin 4) (IcoIdx a m)).aemeasurable
  have hg : AEMeasurable g μ4Measure :=
    (Finset.measurable_restrict (X := fun _ : ℤ => Fin 4) (IcoIdx (a + (m + 1)) n)).aemeasurable
  have hpair :
      μ4Measure.map (fun x : ℤ → Fin 4 => (f x, g x))
        = (μ4Measure.map f).prod (μ4Measure.map g) := by
    -- compute the LHS via interval factorization and identify the marginals
    have hmap :
        μ4Measure.map (fun x : ℤ → Fin 4 => (f x, g x))
          = (intervalMeasure4 a m).prod (intervalMeasure4 (a + (m + 1)) n) := by
      simpa [f, g] using μ4Measure_map_restrict_pair (a := a) (m := m) (n := n)
    have hL : μ4Measure.map f = intervalMeasure4 a m := by
      simpa [f] using μ4Measure_map_restrict_IcoIdx (a := a) (n := m)
    have hR : μ4Measure.map g = intervalMeasure4 (a + (m + 1)) n := by
      simpa [g] using μ4Measure_map_restrict_IcoIdx (a := a + (m + 1)) (n := n)
    simpa [hL, hR] using hmap
  -- `μ4Measure` is finite (probability measure).
  haveI : IsFiniteMeasure μ4Measure := by
    refine MeasureTheory.IsFiniteMeasure.mk ?_
    have hμ : μ4Measure univ = (1 : ℝ≥0∞) := by
      simpa [μ4] using
        (MeasureTheory.IsProbabilityMeasure.measure_univ (μ := (μ4 : Measure (ℤ → Fin 4))))
    simp [hμ]
  exact (indepFun_iff_map_prod_eq_prod_map_map (μ := μ4Measure) hf hg).2 hpair

/-! ### Half-line independence and `1`-dependence -/

/-- σ-algebra of the block `[i-m, i)` as a comap of the restriction map. -/
noncomputable def pastBlockMS (i : ℤ) (m : ℕ) : MeasurableSpace (ℤ → Fin 4) :=
  MeasurableSpace.comap ((IcoIdx (i - m) m).restrict (π := fun _ : ℤ => Fin 4)) inferInstance

/-- σ-algebra of the block `[i+1, i+1+n)` as a comap of the restriction map. -/
noncomputable def futureBlockMS (i : ℤ) (n : ℕ) : MeasurableSpace (ℤ → Fin 4) :=
  MeasurableSpace.comap ((IcoIdx (i + 1) n).restrict (π := fun _ : ℤ => Fin 4)) inferInstance

lemma IcoIdx_past_subset (i : ℤ) {m m' : ℕ} (h : m ≤ m') :
    IcoIdx (i - m) m ⊆ IcoIdx (i - m') m' := by
  intro x hx
  have hxI : i - (m : ℤ) ≤ (x : ℤ) ∧ (x : ℤ) < i - (m : ℤ) + (m : ℤ) := by
    simpa [IcoIdx, sub_eq_add_neg, add_assoc] using (Finset.mem_Ico).1 hx
  have hx_lower : i - (m : ℤ) ≤ (x : ℤ) := hxI.1
  have hx_upper : (x : ℤ) < i := by
    have hi : i - (m : ℤ) + (m : ℤ) = i := by abel
    simpa [hi] using hxI.2
  refine (Finset.mem_Ico).2 ?_
  constructor
  · have hm : (m : ℤ) ≤ (m' : ℤ) := by exact_mod_cast h
    have hle : i - (m' : ℤ) ≤ i - (m : ℤ) := by
      simpa using (sub_le_sub_left hm i)
    exact le_trans hle hx_lower
  · have hi' : i - (m' : ℤ) + (m' : ℤ) = i := by abel
    simpa [hi'] using hx_upper

lemma IcoIdx_future_subset (i : ℤ) {n n' : ℕ} (h : n ≤ n') :
    IcoIdx (i + 1) n ⊆ IcoIdx (i + 1) n' := by
  have hsub : IcoIdx (i + 1) n ⊆ IcoIdx (i + 1) (n + (n' - n)) :=
    Ico_subset_Ico_add (a := i + 1) (n := n) (m := n' - n)
  have hlen : n + (n' - n) = n' := by
    simpa [Nat.add_comm] using (Nat.sub_add_cancel h)
  simpa [hlen] using hsub

lemma pastBlockMS_mono (i : ℤ) : Monotone (pastBlockMS i) := by
  intro m m' h
  have hsub : IcoIdx (i - m) m ⊆ IcoIdx (i - m') m' := IcoIdx_past_subset (i := i) h
  have hmeas : Measurable (Finset.restrict₂ (π := fun _ : ℤ => Fin 4) hsub) := by
    classical
    simpa using measurable_of_finite (Finset.restrict₂ (π := fun _ : ℤ => Fin 4) hsub)
  have hcomp :
      (Finset.restrict₂ (π := fun _ : ℤ => Fin 4) hsub) ∘
          (IcoIdx (i - m') m').restrict (π := fun _ : ℤ => Fin 4)
        = (IcoIdx (i - m) m).restrict (π := fun _ : ℤ => Fin 4) := by
    rfl
  have hle_pi :
      MeasurableSpace.comap (Finset.restrict₂ (π := fun _ : ℤ => Fin 4) hsub)
          (MeasurableSpace.pi : MeasurableSpace (IcoIdx (i - m) m → Fin 4))
        ≤ (MeasurableSpace.pi : MeasurableSpace (IcoIdx (i - m') m' → Fin 4)) :=
    hmeas.comap_le
  simpa [pastBlockMS, hcomp, MeasurableSpace.comap_comp] using
    (MeasurableSpace.comap_mono
      (g := (IcoIdx (i - m') m').restrict (π := fun _ : ℤ => Fin 4)) hle_pi)

lemma futureBlockMS_mono (i : ℤ) : Monotone (futureBlockMS i) := by
  intro n n' h
  have hsub : IcoIdx (i + 1) n ⊆ IcoIdx (i + 1) n' := IcoIdx_future_subset (i := i) h
  have hmeas : Measurable (Finset.restrict₂ (π := fun _ : ℤ => Fin 4) hsub) :=
    Finset.measurable_restrict₂ (X := fun _ : ℤ => Fin 4) hsub
  have hcomp :
      (Finset.restrict₂ (π := fun _ : ℤ => Fin 4) hsub) ∘
          (IcoIdx (i + 1) n').restrict (π := fun _ : ℤ => Fin 4)
        = (IcoIdx (i + 1) n).restrict (π := fun _ : ℤ => Fin 4) := by
    rfl
  have hle_pi :
      MeasurableSpace.comap (Finset.restrict₂ (π := fun _ : ℤ => Fin 4) hsub)
          (MeasurableSpace.pi : MeasurableSpace (IcoIdx (i + 1) n → Fin 4))
        ≤ (MeasurableSpace.pi : MeasurableSpace (IcoIdx (i + 1) n' → Fin 4)) :=
    hmeas.comap_le
  simpa [futureBlockMS, hcomp, MeasurableSpace.comap_comp] using
    (MeasurableSpace.comap_mono
      (g := (IcoIdx (i + 1) n').restrict (π := fun _ : ℤ => Fin 4)) hle_pi)

lemma indep_pastBlockMS_futureBlockMS (i : ℤ) (m n : ℕ) :
    Indep (pastBlockMS i m) (futureBlockMS i n) (μ := μ4Measure) := by
  -- Reduce to `IndepFun` for the restriction maps.
  have hind : ((IcoIdx (i - m) m).restrict) ⟂ᵢ[μ4Measure] ((IcoIdx (i + 1) n).restrict) := by
    -- `a = i - m` and `a + (m+1) = i+1`.
    have ha : i - (m : ℤ) + ((m : ℤ) + 1) = i + 1 := by
      simp [sub_eq_add_neg, add_assoc, add_left_comm]
    have hind' := μ4_indep_restrict_left_right (a := i - m) (m := m) (n := n)
    -- Rewrite the start index of the right interval.
    -- `simp` is not strong enough here because the codomain of the restriction map depends on the
    -- finset, so we use `rw`.
    have hind'' := hind'
    rw [ha] at hind''
    simpa using hind''
  -- Convert to independence of the comapped σ-algebras.
  simpa [pastBlockMS, futureBlockMS, ProbabilityTheory.IndepFun_iff_Indep] using
    (ProbabilityTheory.IndepFun_iff_Indep (f := (IcoIdx (i - m) m).restrict)
      (g := (IcoIdx (i + 1) n).restrict) (μ := μ4Measure)).1 hind

lemma pastMeasurableSpace_le_iSup_pastBlockMS (i : ℤ) :
    pastMeasurableSpace (q := 4) i ≤ ⨆ m : ℕ, pastBlockMS i m := by
  classical
  refine iSup_le ?_
  rintro ⟨j, hjlt⟩
  -- Choose `m = (i - j).toNat`, so that `j ∈ [i-m, i)`.
  let m : ℕ := (i - j).toNat
  have hij : j < i := hjlt
  have hji : j ≤ i := le_of_lt hij
  have hm_nonneg : 0 ≤ i - j := sub_nonneg.2 hji
  have hm_cast : ((i - j).toNat : ℤ) = i - j := Int.toNat_of_nonneg hm_nonneg
  have hjmem : j ∈ IcoIdx (i - m) m := by
    -- `i - m = j` and `i - m + m = i`.
    have hstart : i - (m : ℤ) = j := by
      -- `m` is `(i-j).toNat`.
      subst m
      calc
        i - ((i - j).toNat : ℤ) = i - (i - j) := by
            rw [hm_cast]
        _ = j := by
            abel
    have hend : i - (m : ℤ) + (m : ℤ) = i := by
      -- cancel `m`
      abel
    refine (Finset.mem_Ico).2 ?_
    constructor
    · simp [hstart]
    · -- `j < i`
      have : j < i - (m : ℤ) + (m : ℤ) := by
        simpa [hend] using hij
      simpa [IcoIdx] using this
  -- Coordinate map factors through restriction to the interval.
  let I : Finset ℤ := IcoIdx (i - m) m
  have hcomp :
      (fun x : ℤ → Fin 4 => x j)
        = (fun f : (I → Fin 4) => f ⟨j, hjmem⟩) ∘ (I.restrict (π := fun _ : ℤ => Fin 4)) := by
    funext x
    rfl
  have hmeas_eval :
      Measurable (fun f : (I → Fin 4) => f ⟨j, hjmem⟩) := by
    simpa using (measurable_pi_apply (a := (⟨j, hjmem⟩ : I)))
  have hle_eval :
      MeasurableSpace.comap (fun f : (I → Fin 4) => f ⟨j, hjmem⟩) inferInstance
        ≤ (inferInstance : MeasurableSpace (I → Fin 4)) :=
    hmeas_eval.comap_le
  -- Use `comap_comp` and monotonicity of `comap`.
  have :
      MeasurableSpace.comap (fun x : ℤ → Fin 4 => x j) inferInstance ≤ pastBlockMS i m := by
    have hle_comp :
        MeasurableSpace.comap
            ((fun f : I → Fin 4 => f ⟨j, hjmem⟩) ∘ (I.restrict (π := fun _ : ℤ => Fin 4)))
            inferInstance
          ≤ MeasurableSpace.comap (I.restrict (π := fun _ : ℤ => Fin 4)) inferInstance := by
      simpa [MeasurableSpace.comap_comp] using
        (MeasurableSpace.comap_mono (g := (I.restrict (π := fun _ : ℤ => Fin 4))) hle_eval)
    simpa [pastBlockMS, I, hcomp] using hle_comp
  -- Conclude by bounding by the supremum.
  exact le_trans this (le_iSup (fun m => pastBlockMS i m) m)

lemma futureMeasurableSpace_le_iSup_futureBlockMS (i : ℤ) :
    futureMeasurableSpace (q := 4) i 1 ≤ ⨆ n : ℕ, futureBlockMS i n := by
  classical
  refine iSup_le ?_
  rintro ⟨j, hjge⟩
  -- Put `n = (j - (i+1)).toNat + 1`, so that `j ∈ [i+1, i+1+n)`.
  let n : ℕ := (j - (i + 1)).toNat + 1
  have hji : i + 1 ≤ j := hjge
  have hnonneg : 0 ≤ j - (i + 1) := sub_nonneg.2 hji
  have hcast : ((j - (i + 1)).toNat : ℤ) = j - (i + 1) := Int.toNat_of_nonneg hnonneg
  have hjmem : j ∈ IcoIdx (i + 1) n := by
    have hend : (i + 1 : ℤ) + (n : ℤ) = j + 1 := by
      calc
        (i + 1 : ℤ) + (n : ℤ)
            = (i + 1 : ℤ) + ((j - (i + 1)).toNat : ℤ) + 1 := by
                simp [n, add_assoc]
        _ = (i + 1 : ℤ) + (j - (i + 1)) + 1 := by
                simp [hcast]
        _ = j + 1 := by
                abel
    refine (Finset.mem_Ico).2 ?_
    constructor
    · simpa [IcoIdx] using hji
    · -- `j < i+1+n`
      have : j < (i + 1 : ℤ) + (n : ℤ) := by
        -- from `hend : i+1+n = j+1`
        rw [hend]
        exact lt_add_one j
      simpa [IcoIdx] using this
  let I : Finset ℤ := IcoIdx (i + 1) n
  have hcomp :
      (fun x : ℤ → Fin 4 => x j)
        = (fun f : (I → Fin 4) => f ⟨j, hjmem⟩) ∘ (I.restrict (π := fun _ : ℤ => Fin 4)) := by
    funext x
    rfl
  have hmeas_eval :
      Measurable (fun f : (I → Fin 4) => f ⟨j, hjmem⟩) := by
    simpa using (measurable_pi_apply (a := (⟨j, hjmem⟩ : I)))
  have hle_eval :
      MeasurableSpace.comap (fun f : (I → Fin 4) => f ⟨j, hjmem⟩) inferInstance
        ≤ (inferInstance : MeasurableSpace (I → Fin 4)) :=
    hmeas_eval.comap_le
  have :
      MeasurableSpace.comap (fun x : ℤ → Fin 4 => x j) inferInstance ≤ futureBlockMS i n := by
    have hle_comp :
        MeasurableSpace.comap
            ((fun f : I → Fin 4 => f ⟨j, hjmem⟩) ∘ (I.restrict (π := fun _ : ℤ => Fin 4)))
            inferInstance
          ≤ MeasurableSpace.comap (I.restrict (π := fun _ : ℤ => Fin 4)) inferInstance := by
      simpa [MeasurableSpace.comap_comp] using
        (MeasurableSpace.comap_mono (g := (I.restrict (π := fun _ : ℤ => Fin 4))) hle_eval)
    simpa [futureBlockMS, I, hcomp] using hle_comp
  exact le_trans this (le_iSup (fun n => futureBlockMS i n) n)

theorem μ4_isKDependent : IsKDependent (q := 4) μ4 1 := by
  intro i
  -- Provide the `IsZeroOrProbabilityMeasure` instance needed for `indep_iSup_of_monotone`.
  haveI : MeasureTheory.IsProbabilityMeasure μ4Measure := by
    refine ⟨?_⟩
    simpa [μ4] using
      (MeasureTheory.IsProbabilityMeasure.measure_univ (μ := (μ4 : Measure (ℤ → Fin 4))))
  -- First, build independence for finite blocks and pass to suprema.
  set pastSup : MeasurableSpace (ℤ → Fin 4) := ⨆ m : ℕ, pastBlockMS i m with hpastSup
  set futureSup : MeasurableSpace (ℤ → Fin 4) := ⨆ n : ℕ, futureBlockMS i n with hfutureSup
  have hle_past : ∀ m, pastBlockMS i m ≤ (MeasurableSpace.pi : MeasurableSpace (ℤ → Fin 4)) := by
    intro m
    exact (Finset.measurable_restrict (X := fun _ : ℤ => Fin 4) (IcoIdx (i - m) m)).comap_le
  have hle_future : ∀ n, futureBlockMS i n ≤ (MeasurableSpace.pi : MeasurableSpace (ℤ → Fin 4)) := by
    intro n
    exact (Finset.measurable_restrict (X := fun _ : ℤ => Fin 4) (IcoIdx (i + 1) n)).comap_le

  have hind_past_futureSup : ∀ m, Indep (pastBlockMS i m) futureSup (μ := μ4Measure) := by
    intro m
    -- Apply `indep_iSup_of_monotone` to the future blocks.
    have hfuture :
        Indep (⨆ n : ℕ, futureBlockMS i n) (pastBlockMS i m) (μ := μ4Measure) := by
      have h_indep : ∀ n, Indep (futureBlockMS i n) (pastBlockMS i m) (μ := μ4Measure) := by
        intro n
        exact (indep_pastBlockMS_futureBlockMS (i := i) (m := m) (n := n)).symm
      have hm : Monotone (futureBlockMS i) := futureBlockMS_mono i
      exact ProbabilityTheory.indep_iSup_of_monotone (m := futureBlockMS i) (m1 := pastBlockMS i m)
        (μ := μ4Measure) h_indep hle_future (hle_past m) hm
    -- Symmetrize to match `pastBlockMS` on the left.
    simpa [futureSup, hfutureSup] using hfuture.symm

  have hind_pastSup_futureSup :
      Indep pastSup futureSup (μ := μ4Measure) := by
    -- Apply `indep_iSup_of_monotone` to the past blocks with fixed `futureSup`.
    have h_indep : ∀ m, Indep (pastBlockMS i m) futureSup (μ := μ4Measure) := hind_past_futureSup
    have hm : Monotone (pastBlockMS i) := pastBlockMS_mono i
    simpa [pastSup, hpastSup] using
      ProbabilityTheory.indep_iSup_of_monotone (m := pastBlockMS i) (m1 := futureSup)
        (μ := μ4Measure) h_indep hle_past (by
          -- `futureSup ≤ pi` since it is an `iSup` of sub-σ-algebras of `pi`.
          refine iSup_le ?_
          intro n
          simpa [futureSup, hfutureSup] using hle_future n) hm

  -- Now restrict from the block suprema to the half-line σ-algebras in the definition of `IsKDependent`.
  have hpast_le : pastMeasurableSpace (q := 4) i ≤ pastSup := by
    simpa [pastSup, hpastSup] using pastMeasurableSpace_le_iSup_pastBlockMS (i := i)
  have hfuture_le : futureMeasurableSpace (q := 4) i 1 ≤ futureSup := by
    simpa [futureSup, hfutureSup] using futureMeasurableSpace_le_iSup_futureBlockMS (i := i)

  exact
    ProbabilityTheory.indep_of_indep_of_le_left
      (ProbabilityTheory.indep_of_indep_of_le_right hind_pastSup_futureSup hfuture_le)
      hpast_le

end Word

end FiniteDependence.Coloring
