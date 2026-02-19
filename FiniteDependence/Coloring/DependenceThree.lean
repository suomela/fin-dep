import FiniteDependence.Coloring.PropertiesThree
import Mathlib.MeasureTheory.Measure.Prod
import Mathlib.Tactic

/-!
# 2-dependence of the `q = 3` process

This file proves that the probability measure `Word.μ3` constructed from the projective family
`Word.P3Family` is `2`-dependent, i.e. the past and future σ-algebras separated by two sites are
independent.

The key input is the factorization identity from Holroyd–Liggett (arXiv:1403.2448v4),
already formalized as `Word.sum_P3_insert2` in `FiniteDependence.Coloring/Distributions.lean`.
-/

open scoped BigOperators ENNReal

namespace FiniteDependence.Coloring

namespace Word

open MeasureTheory ProbabilityTheory Set

namespace Three

/-! ## Word-level block maps -/

/-- The first middle index `m` inside `Fin (m+2+n)` (viewed as `Fin ((m+2)+n)`). -/
noncomputable def midIndex0 (m n : ℕ) : Fin (m + 2 + n) :=
  Fin.castAdd n (Fin.castSucc (Fin.last m))

/-- The second middle index `m+1` inside `Fin (m+2+n)` (viewed as `Fin ((m+2)+n)`). -/
noncomputable def midIndex1 (m n : ℕ) : Fin (m + 2 + n) :=
  Fin.castAdd n (Fin.last (m + 1))

/-- The left block of length `m` of a word of length `m+2+n`, skipping the two middle letters. -/
noncomputable def leftPart (m n : ℕ) (w : Word 3 (m + 2 + n)) : Word 3 m :=
  fun i => w (Fin.castAdd n i.castSucc.castSucc)

/-- The right block of length `n` of a word of length `m+2+n`, skipping the two middle letters. -/
noncomputable def rightPart (m n : ℕ) (w : Word 3 (m + 2 + n)) : Word 3 n :=
  fun i => w (Fin.natAdd (m + 2) i)

/-- The pair map `(leftPart, rightPart)`. -/
noncomputable def parts (m n : ℕ) (w : Word 3 (m + 2 + n)) : Word 3 m × Word 3 n :=
  (leftPart m n w, rightPart m n w)

lemma insert2_midIndex0 (m n : ℕ) (x : Word 3 m) (a b : Fin 3) (y : Word 3 n) :
    insert2 (q := 3) (m := m) (n := n) x a b y (midIndex0 m n) = a := by
  simp [midIndex0, insert2, append, snoc]

lemma insert2_midIndex1 (m n : ℕ) (x : Word 3 m) (a b : Fin 3) (y : Word 3 n) :
    insert2 (q := 3) (m := m) (n := n) x a b y (midIndex1 m n) = b := by
  simp [midIndex1, insert2, append, snoc]

lemma insert2_injective (m n : ℕ) (x : Word 3 m) (y : Word 3 n) :
    Function.Injective (fun p : Fin 3 × Fin 3 =>
      insert2 (q := 3) (m := m) (n := n) x p.1 p.2 y) := by
  rintro ⟨a₁, b₁⟩ ⟨a₂, b₂⟩ h
  have ha :
      insert2 (q := 3) (m := m) (n := n) x a₁ b₁ y (midIndex0 m n)
        = insert2 (q := 3) (m := m) (n := n) x a₂ b₂ y (midIndex0 m n) :=
    congrArg (fun w : Word 3 (m + 2 + n) => w (midIndex0 m n)) h
  have hb :
      insert2 (q := 3) (m := m) (n := n) x a₁ b₁ y (midIndex1 m n)
        = insert2 (q := 3) (m := m) (n := n) x a₂ b₂ y (midIndex1 m n) :=
    congrArg (fun w : Word 3 (m + 2 + n) => w (midIndex1 m n)) h
  have ha' : a₁ = a₂ := by
    simpa [insert2_midIndex0 (m := m) (n := n) (x := x) (y := y)] using ha
  have hb' : b₁ = b₂ := by
    simpa [insert2_midIndex1 (m := m) (n := n) (x := x) (y := y)] using hb
  cases ha'
  cases hb'
  rfl

lemma leftPart_insert2 (m n : ℕ) (x : Word 3 m) (a b : Fin 3) (y : Word 3 n) :
    leftPart m n (insert2 (q := 3) (m := m) (n := n) x a b y) = x := by
  funext i
  simp [leftPart, insert2, append, snoc]

lemma rightPart_insert2 (m n : ℕ) (x : Word 3 m) (a b : Fin 3) (y : Word 3 n) :
    rightPart m n (insert2 (q := 3) (m := m) (n := n) x a b y) = y := by
  funext i
  simp [rightPart, insert2, append, snoc]

private lemma exists_insert2_of_parts_eq (m n : ℕ) (x : Word 3 m) (y : Word 3 n)
    (w : Word 3 (m + 2 + n)) (hx : leftPart m n w = x) (hy : rightPart m n w = y) :
    ∃ a b : Fin 3, insert2 (q := 3) (m := m) (n := n) x a b y = w := by
  classical
  refine ⟨w (midIndex0 m n), w (midIndex1 m n), ?_⟩

  -- Split `w` into a left block of length `m+2` and a right block of length `n`.
  have hw :
      Fin.append (fun i : Fin (m + 2) => w (Fin.castAdd n i))
          (fun j : Fin n => w (Fin.natAdd (m + 2) j)) = w := by
    simpa [Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using
      (Fin.append_castAdd_natAdd (f := w) (m := m + 2) (n := n))

  -- Identify the left block with `snoc (snoc x a) b`.
  have hleft :
      (fun i : Fin (m + 2) => w (Fin.castAdd n i)) =
        snoc (q := 3) (n := m + 1) (snoc (q := 3) (n := m) x (w (midIndex0 m n))) (w (midIndex1 m n)) := by
    funext i
    -- Split `i : Fin (m+2)` into: last (`m+1`), second-last (`m`), or an index of `x`.
    refine Fin.lastCases ?_ (fun i1 : Fin (m + 1) => ?_) i
    · -- last index gives `b`
      simp [midIndex1, snoc]
    · -- `i = i1.castSucc`; now split `i1 : Fin (m+1)` into last (`m`) or an index of `x`.
      refine Fin.lastCases ?_ (fun j : Fin m => ?_) i1
      · -- second-last index gives `a`
        -- here `i = (Fin.last m).castSucc`, i.e. `midIndex0`.
        simp [midIndex0, snoc]
      · -- indices of `x`
        have hxj : leftPart m n w j = x j := by
          simpa using congrArg (fun f : Word 3 m => f j) hx
        -- unfold `leftPart` to match the index in the left block
        simp [leftPart] at hxj
        -- `snoc` agrees with its base word on `castSucc` indices (twice).
        simpa [snoc] using hxj

  have hright : (fun j : Fin n => w (Fin.natAdd (m + 2) j)) = y := by
    funext j
    have hyj : rightPart m n w j = y j := by
      simpa using congrArg (fun f : Word 3 n => f j) hy
    simpa [rightPart, hyj]

  -- Reassemble.
  simpa [insert2, append, hleft, hright] using hw

lemma preimage_parts_singleton (m n : ℕ) (x : Word 3 m) (y : Word 3 n) :
    parts m n ⁻¹' ({(x, y)} : Set (Word 3 m × Word 3 n)) =
      (((Finset.univ : Finset (Fin 3)) ×ˢ (Finset.univ : Finset (Fin 3))).image
          (fun p : Fin 3 × Fin 3 =>
            insert2 (q := 3) (m := m) (n := n) x p.1 p.2 y) :
        Set (Word 3 (m + 2 + n))) := by
  ext w
  constructor
  · intro hw
    have hx : leftPart m n w = x := by
      simpa [parts] using congrArg Prod.fst (by simpa [Set.mem_preimage, Set.mem_singleton_iff] using hw)
    have hy : rightPart m n w = y := by
      simpa [parts] using congrArg Prod.snd (by simpa [Set.mem_preimage, Set.mem_singleton_iff] using hw)
    rcases exists_insert2_of_parts_eq (m := m) (n := n) (x := x) (y := y) (w := w) hx hy with ⟨a, b, rfl⟩
    have :
        insert2 (q := 3) (m := m) (n := n) x a b y ∈
          (((Finset.univ : Finset (Fin 3)) ×ˢ (Finset.univ : Finset (Fin 3))).image
            (fun p : Fin 3 × Fin 3 =>
              insert2 (q := 3) (m := m) (n := n) x p.1 p.2 y)) := by
      refine Finset.mem_image.2 ?_
      refine ⟨(a, b), ?_, rfl⟩
      simp
    exact (Finset.mem_coe).2 this
  · intro hw
    have hw' :
        w ∈
          (((Finset.univ : Finset (Fin 3)) ×ˢ (Finset.univ : Finset (Fin 3))).image
            (fun p : Fin 3 × Fin 3 =>
              insert2 (q := 3) (m := m) (n := n) x p.1 p.2 y)) :=
      (Finset.mem_coe).1 hw
    rcases Finset.mem_image.1 hw' with ⟨p, hp, rfl⟩
    rcases p with ⟨a, b⟩
    -- Compute the parts of an inserted word.
    simp [parts, leftPart_insert2, rightPart_insert2]

lemma pmf3_parts_singleton (m n : ℕ) (x : Word 3 m) (y : Word 3 n) :
    (pmf3 (m + 2 + n)).toMeasure
        (parts m n ⁻¹' ({(x, y)} : Set (Word 3 m × Word 3 n)))
      = P3 m x * P3 n y := by
  classical
  rw [preimage_parts_singleton (m := m) (n := n) (x := x) (y := y)]
  -- Switch from a set-coercion to a genuine finset argument.
  set s :
      Finset (Word 3 (m + 2 + n)) :=
    ((Finset.univ : Finset (Fin 3)) ×ˢ (Finset.univ : Finset (Fin 3))).image
      (fun p : Fin 3 × Fin 3 => insert2 (q := 3) (m := m) (n := n) x p.1 p.2 y) with hs
  change (pmf3 (m + 2 + n)).toMeasure s = P3 m x * P3 n y
  -- Evaluate the `PMF` measure on a finset and use injectivity.
  have hinj :
      Set.InjOn (fun p : Fin 3 × Fin 3 =>
          insert2 (q := 3) (m := m) (n := n) x p.1 p.2 y)
        (↑((Finset.univ : Finset (Fin 3)) ×ˢ (Finset.univ : Finset (Fin 3))) : Set (Fin 3 × Fin 3)) := by
    intro p₁ hp₁ p₂ hp₂ h
    exact insert2_injective (m := m) (n := n) (x := x) (y := y) h
  calc
    (pmf3 (m + 2 + n)).toMeasure s
        =
        ∑ w ∈ s, (pmf3 (m + 2 + n)) w := by
          simpa [hs] using
            (PMF.toMeasure_apply_finset (p := pmf3 (m + 2 + n)) (s := s))
    _ =
        ∑ p : Fin 3 × Fin 3,
          (pmf3 (m + 2 + n))
            (insert2 (q := 3) (m := m) (n := n) x p.1 p.2 y) := by
          -- Replace the sum over the image by a sum over `Fin 3 × Fin 3`.
          -- `Finset.sum_image` expects an `InjOn` hypothesis on the domain finset.
          simpa [hs] using
            (Finset.sum_image (f := fun w : Word 3 (m + 2 + n) => (pmf3 (m + 2 + n)) w)
              (s := ((Finset.univ : Finset (Fin 3)) ×ˢ (Finset.univ : Finset (Fin 3))))
              (g := fun p : Fin 3 × Fin 3 =>
                insert2 (q := 3) (m := m) (n := n) x p.1 p.2 y) hinj)
    _ =
        (∑ a : Fin 3, ∑ b : Fin 3,
          (pmf3 (m + 2 + n)) (insert2 (q := 3) (m := m) (n := n) x a b y)) := by
          -- Convert the sum over the product type into an iterated sum.
          simp [Fintype.sum_prod_type]
    _ = P3 m x * P3 n y := by
          -- Unfold `pmf3` and apply the factorization identity.
          simpa [pmf3] using (sum_P3_insert2 (m := m) (n := n) (x := x) (y := y))

lemma pmf3_parts_map (m n : ℕ) :
    Measure.map (parts m n) (pmf3 (m + 2 + n)).toMeasure
      = (pmf3 m).toMeasure.prod (pmf3 n).toMeasure := by
  classical
  refine Measure.ext_of_singleton (α := Word 3 m × Word 3 n) ?_
  rintro ⟨x, y⟩
  have hmeas : MeasurableSet ({(x, y)} : Set (Word 3 m × Word 3 n)) := measurableSet_singleton _
  have hmeas_parts : Measurable (parts m n) := by
    simpa using measurable_of_finite (parts m n)
  have hL :
      Measure.map (parts m n) (pmf3 (m + 2 + n)).toMeasure ({(x, y)} : Set (Word 3 m × Word 3 n))
        = P3 m x * P3 n y := by
      simpa [Measure.map_apply hmeas_parts hmeas] using
        (pmf3_parts_singleton (m := m) (n := n) (x := x) (y := y))
  have hR :
      (pmf3 m).toMeasure.prod (pmf3 n).toMeasure ({(x, y)} : Set (Word 3 m × Word 3 n))
        = P3 m x * P3 n y := by
    have hxy :
        ({(x, y)} : Set (Word 3 m × Word 3 n)) =
          ({x} : Set (Word 3 m)) ×ˢ ({y} : Set (Word 3 n)) := by
      ext z
      simp
    calc
      (pmf3 m).toMeasure.prod (pmf3 n).toMeasure ({(x, y)} : Set (Word 3 m × Word 3 n))
          = (pmf3 m).toMeasure.prod (pmf3 n).toMeasure
              (({x} : Set (Word 3 m)) ×ˢ ({y} : Set (Word 3 n))) := by
              rw [hxy]
      _ = (pmf3 m).toMeasure ({x} : Set (Word 3 m)) * (pmf3 n).toMeasure ({y} : Set (Word 3 n)) := by
              simpa using
                (Measure.prod_prod (μ := (pmf3 m).toMeasure) (ν := (pmf3 n).toMeasure)
                  ({x} : Set (Word 3 m)) ({y} : Set (Word 3 n)))
      _ = (pmf3 m) x * (pmf3 n) y := by simp
      _ = P3 m x * P3 n y := by rfl
  simp [hL, hR]

theorem pmf3_indep_leftPart_rightPart (m n : ℕ) :
    (leftPart m n) ⟂ᵢ[(pmf3 (m + 2 + n)).toMeasure] (rightPart m n) := by
  classical
  let μ : Measure (Word 3 (m + 2 + n)) := (pmf3 (m + 2 + n)).toMeasure
  have hpair :
      μ.map (fun w => (leftPart m n w, rightPart m n w))
        = (pmf3 m).toMeasure.prod (pmf3 n).toMeasure := by
      simpa [μ, parts] using pmf3_parts_map (m := m) (n := n)
  have hf : AEMeasurable (leftPart m n) μ := (measurable_of_finite (leftPart m n)).aemeasurable
  have hg : AEMeasurable (rightPart m n) μ := (measurable_of_finite (rightPart m n)).aemeasurable

  have hμL : μ.map (leftPart m n) = (pmf3 m).toMeasure := by
    have hmeas_pair : Measurable (fun w => (leftPart m n w, rightPart m n w)) := by
      simpa using measurable_of_finite (fun w : Word 3 (m + 2 + n) => (leftPart m n w, rightPart m n w))
    calc
      μ.map (leftPart m n)
          = (μ.map (fun w => (leftPart m n w, rightPart m n w))).map Prod.fst := by
              symm
              have hcomp :
                  (Prod.fst ∘ fun w => (leftPart m n w, rightPart m n w)) = leftPart m n := by
                funext w
                rfl
              simp [Measure.map_map measurable_fst hmeas_pair, hcomp]
      _ = ((pmf3 m).toMeasure.prod (pmf3 n).toMeasure).map Prod.fst := by
            simp [hpair]
      _ = (pmf3 m).toMeasure := by
            simp

  have hμR : μ.map (rightPart m n) = (pmf3 n).toMeasure := by
    have hmeas_pair : Measurable (fun w => (leftPart m n w, rightPart m n w)) := by
      simpa using measurable_of_finite (fun w : Word 3 (m + 2 + n) => (leftPart m n w, rightPart m n w))
    calc
      μ.map (rightPart m n)
          = (μ.map (fun w => (leftPart m n w, rightPart m n w))).map Prod.snd := by
              symm
              have hcomp :
                  (Prod.snd ∘ fun w => (leftPart m n w, rightPart m n w)) = rightPart m n := by
                funext w
                rfl
              simp [Measure.map_map measurable_snd hmeas_pair, hcomp]
      _ = ((pmf3 m).toMeasure.prod (pmf3 n).toMeasure).map Prod.snd := by
            simp [hpair]
      _ = (pmf3 n).toMeasure := by
            simp

  have hpair' :
      μ.map (fun w => (leftPart m n w, rightPart m n w))
        = (μ.map (leftPart m n)).prod (μ.map (rightPart m n)) := by
      simpa [hμL, hμR] using hpair

  haveI : IsFiniteMeasure μ := by
    infer_instance

  exact (indepFun_iff_map_prod_eq_prod_map_map (μ := μ) hf hg).2 hpair'

end Three

/-! ## Interval and half-line independence for `μ3` -/

namespace Three

/-! ### Restriction maps on integer intervals -/

lemma equivIco_symm_val (a : ℤ) (n : ℕ) (i : IcoIdx a n) :
    ((equivIco a n).symm i).1 = (i.1 - a).toNat := by
  cases n with
  | zero =>
      exact (isEmptyElim i)
  | succ n =>
      simp [equivIco]

lemma Ico_left_subset (a : ℤ) (m n : ℕ) : IcoIdx a m ⊆ IcoIdx a (m + 2 + n) := by
  -- Include `[a, a+m)` in `[a, a+m+(n+2))`, then rewrite.
  have hsub : IcoIdx a m ⊆ IcoIdx a (m + (n + 2)) := Ico_subset_Ico_add a m (n + 2)
  simpa [Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using hsub

lemma Ico_right_subset (a : ℤ) (m n : ℕ) : IcoIdx (a + (m + 2)) n ⊆ IcoIdx a (m + 2 + n) := by
  simpa [Nat.add_assoc] using (Ico_shift_subset (a := a) (l := m + 2) (n := n))

/-- Restrict an assignment on `[a, a+m+2+n)` to the left block `[a, a+m)`. -/
noncomputable def icoLeft (a : ℤ) (m n : ℕ) :
    (IcoIdx a (m + 2 + n) → Fin 3) → (IcoIdx a m → Fin 3) :=
  Finset.restrict₂ (π := fun _ : ℤ => Fin 3) (Ico_left_subset a m n)

/-- Restrict an assignment on `[a, a+m+2+n)` to the right block `[a+m+2, a+m+2+n)`. -/
noncomputable def icoRight (a : ℤ) (m n : ℕ) :
    (IcoIdx a (m + 2 + n) → Fin 3) → (IcoIdx (a + (m + 2)) n → Fin 3) :=
  Finset.restrict₂ (π := fun _ : ℤ => Fin 3) (Ico_right_subset a m n)

/-- The pair map of left and right restrictions. -/
noncomputable def icoParts (a : ℤ) (m n : ℕ) :
    (IcoIdx a (m + 2 + n) → Fin 3) →
      (IcoIdx a m → Fin 3) × (IcoIdx (a + (m + 2)) n → Fin 3) :=
  fun f => (icoLeft a m n f, icoRight a m n f)

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

lemma icoLeft_wordToIco (a : ℤ) (m n : ℕ) (w : Word 3 (m + 2 + n)) :
    icoLeft a m n (wordToIco (q := 3) a (m + 2 + n) w) =
      wordToIco (q := 3) a m (leftPart m n w) := by
  classical
  funext i
  cases m with
  | zero =>
      exact (isEmptyElim i)
  | succ m =>
      let iBig : IcoIdx a (Nat.succ m + 2 + n) := ⟨i.1, Ico_left_subset a (Nat.succ m) n i.2⟩
      have hidx :
          (equivIco a (Nat.succ m + 2 + n)).symm iBig
            = Fin.castAdd n ((equivIco a (Nat.succ m)).symm i).castSucc.castSucc := by
        apply Fin.ext
        have hLval :
            ((equivIco a (Nat.succ m + 2 + n)).symm iBig).1 = (i.1 - a).toNat := by
          simpa [iBig] using equivIco_symm_val (a := a) (n := Nat.succ m + 2 + n) iBig
        have hSmall : ((equivIco a (Nat.succ m)).symm i).1 = (i.1 - a).toNat := by
          simpa using equivIco_symm_val (a := a) (n := Nat.succ m) i
        have hRval :
            (Fin.castAdd n (((equivIco a (Nat.succ m)).symm i).castSucc.castSucc)).1 = (i.1 - a).toNat := by
          simpa using hSmall
        exact hLval.trans hRval.symm
      simp [icoLeft, wordToIco, leftPart, iBig, hidx]

lemma icoRight_wordToIco (a : ℤ) (m n : ℕ) (w : Word 3 (m + 2 + n)) :
    icoRight a m n (wordToIco (q := 3) a (m + 2 + n) w) =
      wordToIco (q := 3) (a + (m + 2)) n (rightPart m n w) := by
  classical
  funext i
  let iBig : IcoIdx a (m + 2 + n) := ⟨i.1, Ico_right_subset a m n i.2⟩
  have hidx :
      (equivIco a (m + 2 + n)).symm iBig =
        Fin.natAdd (m + 2) ((equivIco (a + (m + 2)) n).symm i) := by
    apply Fin.ext
    have hLval : ((equivIco a (m + 2 + n)).symm iBig).1 = (i.1 - a).toNat := by
      simpa [iBig] using equivIco_symm_val (a := a) (n := m + 2 + n) iBig
    have hi : a + (m + 2) ≤ i.1 := (Finset.mem_Ico).1 i.2 |>.1
    have hsplit : (i.1 - a).toNat = (m + 2) + (i.1 - (a + (m + 2))).toNat := by
      simpa [sub_eq_add_neg, add_assoc] using
        (toNat_sub_eq_add_toNat_sub (a := a) (b := i.1) (m := m + 2) hi)
    have hRbase : ((equivIco (a + (m + 2)) n).symm i).1 = (i.1 - (a + (m + 2))).toNat := by
      simpa using equivIco_symm_val (a := a + (m + 2)) (n := n) i
    have hRval :
        (Fin.natAdd (m + 2) ((equivIco (a + (m + 2)) n).symm i)).1 = (i.1 - a).toNat := by
      simp [Fin.natAdd, hRbase, hsplit]
    exact hLval.trans hRval.symm
  simp [icoRight, wordToIco, rightPart, iBig, hidx]

lemma icoParts_wordToIco (a : ℤ) (m n : ℕ) (w : Word 3 (m + 2 + n)) :
    icoParts a m n (wordToIco (q := 3) a (m + 2 + n) w)
      = (wordToIco (q := 3) a m (leftPart m n w),
        wordToIco (q := 3) (a + (m + 2)) n (rightPart m n w)) := by
  ext <;> simp [icoParts, icoLeft_wordToIco, icoRight_wordToIco]

theorem intervalMeasure3_map_icoParts (a : ℤ) (m n : ℕ) :
    Measure.map (icoParts a m n) (intervalMeasure3 a (m + 2 + n))
      = (intervalMeasure3 a m).prod (intervalMeasure3 (a + (m + 2)) n) := by
  classical
  have hmeas_word : Measurable (wordToIco (q := 3) a (m + 2 + n)) := by
    simpa using (measurable_of_finite (wordToIco (q := 3) a (m + 2 + n)))
  have hmeas_icoParts : Measurable (icoParts a m n) := by
    simpa using measurable_of_finite (icoParts a m n)
  calc
    Measure.map (icoParts a m n) (intervalMeasure3 a (m + 2 + n))
        = Measure.map (icoParts a m n ∘ wordToIco (q := 3) a (m + 2 + n))
            (pmf3 (m + 2 + n)).toMeasure := by
              simp [intervalMeasure3, Measure.map_map hmeas_icoParts hmeas_word]
    _ = Measure.map (fun w : Word 3 (m + 2 + n) =>
          (wordToIco (q := 3) a m (leftPart m n w),
            wordToIco (q := 3) (a + (m + 2)) n (rightPart m n w)))
          (pmf3 (m + 2 + n)).toMeasure := by
          refine congrArg (fun f => Measure.map f (pmf3 (m + 2 + n)).toMeasure) ?_
          funext w
          simp [Function.comp, icoParts_wordToIco (a := a) (m := m) (n := n) (w := w)]
    _ = Measure.map
          (Prod.map (wordToIco (q := 3) a m) (wordToIco (q := 3) (a + (m + 2)) n))
          (Measure.map (parts m n) (pmf3 (m + 2 + n)).toMeasure) := by
          have hmeas_parts : Measurable (parts m n) := by
            simpa using measurable_of_finite (parts m n)
          have hmeas_prod :
              Measurable
                (Prod.map (wordToIco (q := 3) a m) (wordToIco (q := 3) (a + (m + 2)) n)) := by
            simpa using measurable_of_finite
              (Prod.map (wordToIco (q := 3) a m) (wordToIco (q := 3) (a + (m + 2)) n))
          have hfun :
              (fun w : Word 3 (m + 2 + n) =>
                  (wordToIco (q := 3) a m (leftPart m n w),
                    wordToIco (q := 3) (a + (m + 2)) n (rightPart m n w)))
                =
                (Prod.map (wordToIco (q := 3) a m) (wordToIco (q := 3) (a + (m + 2)) n)) ∘
                  parts m n := by
            funext w
            simp [Function.comp, parts]
          calc
            Measure.map (fun w : Word 3 (m + 2 + n) =>
                (wordToIco (q := 3) a m (leftPart m n w),
                  wordToIco (q := 3) (a + (m + 2)) n (rightPart m n w)))
                (pmf3 (m + 2 + n)).toMeasure
                =
                Measure.map
                  ((Prod.map (wordToIco (q := 3) a m) (wordToIco (q := 3) (a + (m + 2)) n)) ∘
                    parts m n)
                  (pmf3 (m + 2 + n)).toMeasure := by
                  simp [hfun]
            _ = Measure.map
                  (Prod.map (wordToIco (q := 3) a m) (wordToIco (q := 3) (a + (m + 2)) n))
                  (Measure.map (parts m n) (pmf3 (m + 2 + n)).toMeasure) := by
                  symm
                  simp [Measure.map_map hmeas_prod hmeas_parts]
    _ = Measure.map
          (Prod.map (wordToIco (q := 3) a m) (wordToIco (q := 3) (a + (m + 2)) n))
          ((pmf3 m).toMeasure.prod (pmf3 n).toMeasure) := by
          simp [pmf3_parts_map (m := m) (n := n)]
    _ = (intervalMeasure3 a m).prod (intervalMeasure3 (a + (m + 2)) n) := by
          have hmeas_left : Measurable (wordToIco (q := 3) a m) := by
            simpa using (measurable_of_finite (wordToIco (q := 3) a m))
          have hmeas_right : Measurable (wordToIco (q := 3) (a + (m + 2)) n) := by
            simpa using (measurable_of_finite (wordToIco (q := 3) (a + (m + 2)) n))
          symm
          simpa [intervalMeasure3] using
            (Measure.map_prod_map (μa := (pmf3 m).toMeasure) (μc := (pmf3 n).toMeasure)
              (f := wordToIco (q := 3) a m) (g := wordToIco (q := 3) (a + (m + 2)) n)
              hmeas_left hmeas_right)

end Three

/-! ### Finite-block independence for `μ3` -/

lemma P3Family_IcoIdx (a : ℤ) : ∀ n : ℕ, P3Family (IcoIdx a n) = intervalMeasure3 a n
  | 0 => by
      classical
      refine Measure.ext_of_singleton (α := (IcoIdx a 0 → Fin 3)) ?_
      intro f
      have hf : f = (fun _ : IcoIdx a 0 => (0 : Fin 3)) := by
        funext i
        exact (isEmptyElim i)
      subst hf
      have hP : P3Family (IcoIdx a 0) = Measure.dirac (fun _ : IcoIdx a 0 => (0 : Fin 3)) := by
        simp [P3Family]
      have hsing :
          ({(fun _ : IcoIdx a 0 => (0 : Fin 3))} : Set (IcoIdx a 0 → Fin 3)) = Set.univ := by
        ext g
        have : g = (fun _ : IcoIdx a 0 => (0 : Fin 3)) := by
          funext i
          exact (isEmptyElim i)
        simp [this]
      have hleft :
          P3Family (IcoIdx a 0)
              ({(fun _ : IcoIdx a 0 => (0 : Fin 3))} : Set (IcoIdx a 0 → Fin 3))
            = 1 := by
        simp [hP]
      have hright :
          intervalMeasure3 a 0 ({(fun _ : IcoIdx a 0 => (0 : Fin 3))} : Set (IcoIdx a 0 → Fin 3))
            = 1 := by
        rw [hsing]
        have hmeas : Measurable (wordToIco (q := 3) a 0) := by
          simpa using (measurable_of_finite (wordToIco (q := 3) a 0))
        simp [intervalMeasure3, Measure.map_apply hmeas MeasurableSet.univ]
      simp [hleft, hright]
  | n + 1 => by
      simpa using (P3Family_IcoIdx_succ (a := a) (n := n))

lemma μ3Measure_map_restrict_IcoIdx (a : ℤ) (n : ℕ) :
    μ3Measure.map (IcoIdx a n).restrict = intervalMeasure3 a n := by
  have hproj := μ3_isProjectiveLimit (I := IcoIdx a n)
  simpa [P3Family_IcoIdx (a := a) n] using hproj

lemma μ3Measure_map_restrict_pair (a : ℤ) (m n : ℕ) :
    μ3Measure.map (fun x : ℤ → Fin 3 =>
        ((IcoIdx a m).restrict x, (IcoIdx (a + (m + 2)) n).restrict x))
      = (intervalMeasure3 a m).prod (intervalMeasure3 (a + (m + 2)) n) := by
  classical
  set I : Finset ℤ := IcoIdx a (m + 2 + n) with hI
  have hmeas_restrict :
      Measurable (I.restrict : (ℤ → Fin 3) → I → Fin 3) :=
    measurable_pi_lambda _ (fun _ => measurable_pi_apply _)
  have hmeas_parts : Measurable (Three.icoParts a m n) := by
    simpa using measurable_of_finite (Three.icoParts a m n)
  have hcomp :
      (fun x : ℤ → Fin 3 => ((IcoIdx a m).restrict x, (IcoIdx (a + (m + 2)) n).restrict x))
        = (Three.icoParts a m n) ∘ (I.restrict : (ℤ → Fin 3) → I → Fin 3) := by
    funext x
    ext <;> rfl
  calc
    μ3Measure.map (fun x : ℤ → Fin 3 =>
        ((IcoIdx a m).restrict x, (IcoIdx (a + (m + 2)) n).restrict x))
        = (μ3Measure.map (I.restrict : (ℤ → Fin 3) → I → Fin 3)).map (Three.icoParts a m n) := by
            simp [hcomp, Measure.map_map hmeas_parts hmeas_restrict]
    _ = (P3Family I).map (Three.icoParts a m n) := by
            simp [μ3_isProjectiveLimit (I := I)]
    _ = (intervalMeasure3 a (m + 2 + n)).map (Three.icoParts a m n) := by
            subst I
            simp [P3Family_IcoIdx (a := a) (n := m + 2 + n)]
    _ = (intervalMeasure3 a m).prod (intervalMeasure3 (a + (m + 2)) n) := by
            simpa using (Three.intervalMeasure3_map_icoParts (a := a) (m := m) (n := n))

theorem μ3_indep_restrict_left_right (a : ℤ) (m n : ℕ) :
    ((IcoIdx a m).restrict) ⟂ᵢ[μ3Measure] ((IcoIdx (a + (m + 2)) n).restrict) := by
  classical
  let f : (ℤ → Fin 3) → (IcoIdx a m → Fin 3) := (IcoIdx a m).restrict
  let g : (ℤ → Fin 3) → (IcoIdx (a + (m + 2)) n → Fin 3) := (IcoIdx (a + (m + 2)) n).restrict
  have hf : AEMeasurable f μ3Measure :=
    (Finset.measurable_restrict (X := fun _ : ℤ => Fin 3) (IcoIdx a m)).aemeasurable
  have hg : AEMeasurable g μ3Measure :=
    (Finset.measurable_restrict (X := fun _ : ℤ => Fin 3) (IcoIdx (a + (m + 2)) n)).aemeasurable
  have hpair :
      μ3Measure.map (fun x : ℤ → Fin 3 => (f x, g x))
        = (μ3Measure.map f).prod (μ3Measure.map g) := by
    have hmap :
        μ3Measure.map (fun x : ℤ → Fin 3 => (f x, g x))
          = (intervalMeasure3 a m).prod (intervalMeasure3 (a + (m + 2)) n) := by
      simpa [f, g] using μ3Measure_map_restrict_pair (a := a) (m := m) (n := n)
    have hL : μ3Measure.map f = intervalMeasure3 a m := by
      simpa [f] using μ3Measure_map_restrict_IcoIdx (a := a) (n := m)
    have hR : μ3Measure.map g = intervalMeasure3 (a + (m + 2)) n := by
      simpa [g] using μ3Measure_map_restrict_IcoIdx (a := a + (m + 2)) (n := n)
    simpa [hL, hR] using hmap
  haveI : IsFiniteMeasure μ3Measure := by
    refine MeasureTheory.IsFiniteMeasure.mk ?_
    have hμ : μ3Measure univ = (1 : ℝ≥0∞) := by
      simpa [μ3] using
        (MeasureTheory.IsProbabilityMeasure.measure_univ (μ := (μ3 : Measure (ℤ → Fin 3))))
    simp [hμ]
  exact (indepFun_iff_map_prod_eq_prod_map_map (μ := μ3Measure) hf hg).2 hpair

/-! ### Half-line independence and `2`-dependence -/

namespace Three

/-- σ-algebra of the block `[i-m, i)` as a comap of the restriction map. -/
noncomputable def pastBlockMS (i : ℤ) (m : ℕ) : MeasurableSpace (ℤ → Fin 3) :=
  MeasurableSpace.comap ((IcoIdx (i - m) m).restrict (π := fun _ : ℤ => Fin 3)) inferInstance

/-- σ-algebra of the block `[i+2, i+2+n)` as a comap of the restriction map. -/
noncomputable def futureBlockMS (i : ℤ) (n : ℕ) : MeasurableSpace (ℤ → Fin 3) :=
  MeasurableSpace.comap ((IcoIdx (i + 2) n).restrict (π := fun _ : ℤ => Fin 3)) inferInstance

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
    IcoIdx (i + 2) n ⊆ IcoIdx (i + 2) n' := by
  have hsub : IcoIdx (i + 2) n ⊆ IcoIdx (i + 2) (n + (n' - n)) :=
    Ico_subset_Ico_add (a := i + 2) (n := n) (m := n' - n)
  have hlen : n + (n' - n) = n' := by
    simpa [Nat.add_comm] using (Nat.sub_add_cancel h)
  simpa [hlen] using hsub

lemma pastBlockMS_mono (i : ℤ) : Monotone (pastBlockMS i) := by
  intro m m' h
  have hsub : IcoIdx (i - m) m ⊆ IcoIdx (i - m') m' := IcoIdx_past_subset (i := i) h
  have hmeas : Measurable (Finset.restrict₂ (π := fun _ : ℤ => Fin 3) hsub) := by
    classical
    simpa using measurable_of_finite (Finset.restrict₂ (π := fun _ : ℤ => Fin 3) hsub)
  have hcomp :
      (Finset.restrict₂ (π := fun _ : ℤ => Fin 3) hsub) ∘
          (IcoIdx (i - m') m').restrict (π := fun _ : ℤ => Fin 3)
        = (IcoIdx (i - m) m).restrict (π := fun _ : ℤ => Fin 3) := by
    rfl
  have hle_pi :
      MeasurableSpace.comap (Finset.restrict₂ (π := fun _ : ℤ => Fin 3) hsub)
          (MeasurableSpace.pi : MeasurableSpace (IcoIdx (i - m) m → Fin 3))
        ≤ (MeasurableSpace.pi : MeasurableSpace (IcoIdx (i - m') m' → Fin 3)) :=
    hmeas.comap_le
  simpa [pastBlockMS, hcomp, MeasurableSpace.comap_comp] using
    (MeasurableSpace.comap_mono
      (g := (IcoIdx (i - m') m').restrict (π := fun _ : ℤ => Fin 3)) hle_pi)

lemma futureBlockMS_mono (i : ℤ) : Monotone (futureBlockMS i) := by
  intro n n' h
  have hsub : IcoIdx (i + 2) n ⊆ IcoIdx (i + 2) n' := IcoIdx_future_subset (i := i) h
  have hmeas : Measurable (Finset.restrict₂ (π := fun _ : ℤ => Fin 3) hsub) :=
    Finset.measurable_restrict₂ (X := fun _ : ℤ => Fin 3) hsub
  have hcomp :
      (Finset.restrict₂ (π := fun _ : ℤ => Fin 3) hsub) ∘
          (IcoIdx (i + 2) n').restrict (π := fun _ : ℤ => Fin 3)
        = (IcoIdx (i + 2) n).restrict (π := fun _ : ℤ => Fin 3) := by
    rfl
  have hle_pi :
      MeasurableSpace.comap (Finset.restrict₂ (π := fun _ : ℤ => Fin 3) hsub)
          (MeasurableSpace.pi : MeasurableSpace (IcoIdx (i + 2) n → Fin 3))
        ≤ (MeasurableSpace.pi : MeasurableSpace (IcoIdx (i + 2) n' → Fin 3)) :=
    hmeas.comap_le
  simpa [futureBlockMS, hcomp, MeasurableSpace.comap_comp] using
    (MeasurableSpace.comap_mono
      (g := (IcoIdx (i + 2) n').restrict (π := fun _ : ℤ => Fin 3)) hle_pi)

lemma indep_pastBlockMS_futureBlockMS (i : ℤ) (m n : ℕ) :
    Indep (pastBlockMS i m) (futureBlockMS i n) (μ := μ3Measure) := by
  have hind :
      ((IcoIdx (i - m) m).restrict) ⟂ᵢ[μ3Measure] ((IcoIdx (i + 2) n).restrict) := by
    have ha : i - (m : ℤ) + ((m : ℤ) + 2) = i + 2 := by
      simp [sub_eq_add_neg, add_assoc, add_left_comm]
    have hind' := μ3_indep_restrict_left_right (a := i - m) (m := m) (n := n)
    have hind'' := hind'
    rw [ha] at hind''
    simpa using hind''
  simpa [pastBlockMS, futureBlockMS, ProbabilityTheory.IndepFun_iff_Indep] using
    (ProbabilityTheory.IndepFun_iff_Indep (f := (IcoIdx (i - m) m).restrict)
      (g := (IcoIdx (i + 2) n).restrict) (μ := μ3Measure)).1 hind

lemma pastMeasurableSpace_le_iSup_pastBlockMS (i : ℤ) :
    pastMeasurableSpace (q := 3) i ≤ ⨆ m : ℕ, pastBlockMS i m := by
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
    have hstart : i - (m : ℤ) = j := by
      subst m
      calc
        i - ((i - j).toNat : ℤ) = i - (i - j) := by
            rw [hm_cast]
        _ = j := by
            abel
    have hend : i - (m : ℤ) + (m : ℤ) = i := by
      abel
    refine (Finset.mem_Ico).2 ?_
    constructor
    · simp [hstart]
    · have : j < i - (m : ℤ) + (m : ℤ) := by
        simpa [hend] using hij
      simpa [IcoIdx] using this
  -- Coordinate map factors through restriction to the interval.
  let I : Finset ℤ := IcoIdx (i - m) m
  have hcomp :
      (fun x : ℤ → Fin 3 => x j)
        = (fun f : (I → Fin 3) => f ⟨j, hjmem⟩) ∘ (I.restrict (π := fun _ : ℤ => Fin 3)) := by
    funext x
    rfl
  have hmeas_eval :
      Measurable (fun f : (I → Fin 3) => f ⟨j, hjmem⟩) := by
    simpa using (measurable_pi_apply (a := (⟨j, hjmem⟩ : I)))
  have hle_eval :
      MeasurableSpace.comap (fun f : (I → Fin 3) => f ⟨j, hjmem⟩) inferInstance
        ≤ (inferInstance : MeasurableSpace (I → Fin 3)) :=
    hmeas_eval.comap_le
  have :
      MeasurableSpace.comap (fun x : ℤ → Fin 3 => x j) inferInstance ≤ pastBlockMS i m := by
    have hle_comp :
        MeasurableSpace.comap
            ((fun f : I → Fin 3 => f ⟨j, hjmem⟩) ∘ (I.restrict (π := fun _ : ℤ => Fin 3)))
            inferInstance
          ≤ MeasurableSpace.comap (I.restrict (π := fun _ : ℤ => Fin 3)) inferInstance := by
      simpa [MeasurableSpace.comap_comp] using
        (MeasurableSpace.comap_mono (g := (I.restrict (π := fun _ : ℤ => Fin 3))) hle_eval)
    simpa [pastBlockMS, I, hcomp] using hle_comp
  exact le_trans this (le_iSup (fun m => pastBlockMS i m) m)

lemma futureMeasurableSpace_le_iSup_futureBlockMS (i : ℤ) :
    futureMeasurableSpace (q := 3) i 2 ≤ ⨆ n : ℕ, futureBlockMS i n := by
  classical
  refine iSup_le ?_
  rintro ⟨j, hjge⟩
  -- Put `n = (j - (i+2)).toNat + 1`, so that `j ∈ [i+2, i+2+n)`.
  let n : ℕ := (j - (i + 2)).toNat + 1
  have hji : i + 2 ≤ j := hjge
  have hnonneg : 0 ≤ j - (i + 2) := sub_nonneg.2 hji
  have hcast : ((j - (i + 2)).toNat : ℤ) = j - (i + 2) := Int.toNat_of_nonneg hnonneg
  have hjmem : j ∈ IcoIdx (i + 2) n := by
    have hend : (i + 2 : ℤ) + (n : ℤ) = j + 1 := by
      calc
        (i + 2 : ℤ) + (n : ℤ)
            = (i + 2 : ℤ) + ((j - (i + 2)).toNat : ℤ) + 1 := by
                simp [n, add_assoc]
        _ = (i + 2 : ℤ) + (j - (i + 2)) + 1 := by
                simp [hcast]
        _ = j + 1 := by
                abel
    refine (Finset.mem_Ico).2 ?_
    constructor
    · simpa [IcoIdx] using hji
    · have : j < (i + 2 : ℤ) + (n : ℤ) := by
        rw [hend]
        exact lt_add_one j
      simpa [IcoIdx] using this
  let I : Finset ℤ := IcoIdx (i + 2) n
  have hcomp :
      (fun x : ℤ → Fin 3 => x j)
        = (fun f : (I → Fin 3) => f ⟨j, hjmem⟩) ∘ (I.restrict (π := fun _ : ℤ => Fin 3)) := by
    funext x
    rfl
  have hmeas_eval :
      Measurable (fun f : (I → Fin 3) => f ⟨j, hjmem⟩) := by
    simpa using (measurable_pi_apply (a := (⟨j, hjmem⟩ : I)))
  have hle_eval :
      MeasurableSpace.comap (fun f : (I → Fin 3) => f ⟨j, hjmem⟩) inferInstance
        ≤ (inferInstance : MeasurableSpace (I → Fin 3)) :=
    hmeas_eval.comap_le
  have :
      MeasurableSpace.comap (fun x : ℤ → Fin 3 => x j) inferInstance ≤ futureBlockMS i n := by
    have hle_comp :
        MeasurableSpace.comap
            ((fun f : I → Fin 3 => f ⟨j, hjmem⟩) ∘ (I.restrict (π := fun _ : ℤ => Fin 3)))
            inferInstance
          ≤ MeasurableSpace.comap (I.restrict (π := fun _ : ℤ => Fin 3)) inferInstance := by
      simpa [MeasurableSpace.comap_comp] using
        (MeasurableSpace.comap_mono (g := (I.restrict (π := fun _ : ℤ => Fin 3))) hle_eval)
    simpa [futureBlockMS, I, hcomp] using hle_comp
  exact le_trans this (le_iSup (fun n => futureBlockMS i n) n)

end Three

theorem μ3_isKDependent : IsKDependent (q := 3) μ3 2 := by
  intro i
  -- Provide the `IsProbabilityMeasure` instance needed for `indep_iSup_of_monotone`.
  haveI : MeasureTheory.IsProbabilityMeasure μ3Measure := by
    refine ⟨?_⟩
    simpa [μ3] using
      (MeasureTheory.IsProbabilityMeasure.measure_univ (μ := (μ3 : Measure (ℤ → Fin 3))))
  -- First, build independence for finite blocks and pass to suprema.
  set pastSup : MeasurableSpace (ℤ → Fin 3) := ⨆ m : ℕ, Three.pastBlockMS i m with hpastSup
  set futureSup : MeasurableSpace (ℤ → Fin 3) := ⨆ n : ℕ, Three.futureBlockMS i n with hfutureSup
  have hle_past :
      ∀ m, Three.pastBlockMS i m ≤ (MeasurableSpace.pi : MeasurableSpace (ℤ → Fin 3)) := by
    intro m
    exact (Finset.measurable_restrict (X := fun _ : ℤ => Fin 3) (IcoIdx (i - m) m)).comap_le
  have hle_future :
      ∀ n, Three.futureBlockMS i n ≤ (MeasurableSpace.pi : MeasurableSpace (ℤ → Fin 3)) := by
    intro n
    exact (Finset.measurable_restrict (X := fun _ : ℤ => Fin 3) (IcoIdx (i + 2) n)).comap_le

  have hind_past_futureSup :
      ∀ m, Indep (Three.pastBlockMS i m) futureSup (μ := μ3Measure) := by
    intro m
    -- Apply `indep_iSup_of_monotone` to the future blocks.
    have hfuture :
        Indep (⨆ n : ℕ, Three.futureBlockMS i n) (Three.pastBlockMS i m) (μ := μ3Measure) := by
      have h_indep :
          ∀ n, Indep (Three.futureBlockMS i n) (Three.pastBlockMS i m) (μ := μ3Measure) := by
        intro n
        exact (Three.indep_pastBlockMS_futureBlockMS (i := i) (m := m) (n := n)).symm
      have hm : Monotone (Three.futureBlockMS i) := Three.futureBlockMS_mono i
      exact ProbabilityTheory.indep_iSup_of_monotone (m := Three.futureBlockMS i) (m1 := Three.pastBlockMS i m)
        (μ := μ3Measure) h_indep hle_future (hle_past m) hm
    -- Symmetrize to match `pastBlockMS` on the left.
    simpa [futureSup, hfutureSup] using hfuture.symm

  have hind_pastSup_futureSup :
      Indep pastSup futureSup (μ := μ3Measure) := by
    -- Apply `indep_iSup_of_monotone` to the past blocks with fixed `futureSup`.
    have h_indep :
        ∀ m, Indep (Three.pastBlockMS i m) futureSup (μ := μ3Measure) := hind_past_futureSup
    have hm : Monotone (Three.pastBlockMS i) := Three.pastBlockMS_mono i
    simpa [pastSup, hpastSup] using
      ProbabilityTheory.indep_iSup_of_monotone (m := Three.pastBlockMS i) (m1 := futureSup)
        (μ := μ3Measure) h_indep hle_past (by
          -- `futureSup ≤ pi` since it is an `iSup` of sub-σ-algebras of `pi`.
          refine iSup_le ?_
          intro n
          simpa [futureSup, hfutureSup] using hle_future n) hm

  -- Restrict from the block suprema to the half-line σ-algebras in the definition of `IsKDependent`.
  have hpast_le : pastMeasurableSpace (q := 3) i ≤ pastSup := by
    simpa [pastSup, hpastSup] using Three.pastMeasurableSpace_le_iSup_pastBlockMS (i := i)
  have hfuture_le : futureMeasurableSpace (q := 3) i 2 ≤ futureSup := by
    simpa [futureSup, hfutureSup] using Three.futureMeasurableSpace_le_iSup_futureBlockMS (i := i)

  exact
    ProbabilityTheory.indep_of_indep_of_le_left
      (ProbabilityTheory.indep_of_indep_of_le_right hind_pastSup_futureSup hfuture_le)
      hpast_le

end Word

end FiniteDependence.Coloring
