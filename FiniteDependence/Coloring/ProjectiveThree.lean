import FiniteDependence.Coloring.ConstructionThree
import FiniteDependence.Coloring.ProjectiveFour
import Mathlib.MeasureTheory.Constructions.ProjectiveFamilyContent
import Mathlib.MeasureTheory.OuterMeasure.OfAddContent
import Mathlib.Topology.Algebra.InfiniteSum.ENNReal

/-!
# The `q = 3` projective family and its projective limit measure

We assemble the interval measures `Word.intervalMeasure3 a n` into a projective family indexed by
finite sets `I : Finset ℤ`, by restricting the measure on the convex hull (integer interval) of
`I` down to `I`.

We then build an additive content on the measurable cylinders from this projective family, prove
the σ-subadditivity condition needed by Carathéodory, and obtain a probability measure on
`ℤ → Fin 3`.
-/

open scoped ENNReal BigOperators Topology

namespace FiniteDependence.Coloring

namespace Word

open MeasureTheory Set

/-! ## Iterated interval restrictions -/

lemma intervalMeasure3_map_restrict_addRight (a : ℤ) (n r : ℕ) :
    (intervalMeasure3 a (n + r)).map
        (Finset.restrict₂ (π := fun _ : ℤ => Fin 3) (Ico_subset_Ico_add a n r))
      = intervalMeasure3 a n := by
  classical
  induction r with
  | zero =>
      have hsub : IcoIdx a n ⊆ IcoIdx a (n + 0) := Ico_subset_Ico_add a n 0
      have hid :
          (Finset.restrict₂ (π := fun _ : ℤ => Fin 3) hsub) = (id : (IcoIdx a n → Fin 3) → _) := by
        funext f
        ext i
        rfl
      simp [hid, Nat.add_zero]
  | succ r ih =>
      -- Drop the last coordinate, then use the inductive hypothesis.
      have hmeas₁ :
          Measurable
            (Finset.restrict₂ (π := fun _ : ℤ => Fin 3) (Ico_subset_Ico_succ a (n + r))) :=
        Finset.measurable_restrict₂ (X := fun _ : ℤ => Fin 3) (Ico_subset_Ico_succ a (n + r))
      have hmeas₂ :
          Measurable (Finset.restrict₂ (π := fun _ : ℤ => Fin 3) (Ico_subset_Ico_add a n r)) :=
        Finset.measurable_restrict₂ (X := fun _ : ℤ => Fin 3) (Ico_subset_Ico_add a n r)
      have hcomp :
          (Finset.restrict₂ (π := fun _ : ℤ => Fin 3) (Ico_subset_Ico_add a n r)) ∘
              (Finset.restrict₂ (π := fun _ : ℤ => Fin 3) (Ico_subset_Ico_succ a (n + r)))
            = Finset.restrict₂ (π := fun _ : ℤ => Fin 3)
                ((Ico_subset_Ico_add a n r).trans (Ico_subset_Ico_succ a (n + r))) := by
        rfl
      have hsub' :
          Finset.restrict₂ (π := fun _ : ℤ => Fin 3)
              ((Ico_subset_Ico_add a n r).trans (Ico_subset_Ico_succ a (n + r)))
            = Finset.restrict₂ (π := fun _ : ℤ => Fin 3) (Ico_subset_Ico_add a n (r + 1)) := by
        exact restrict₂_eq_of_eq (π := fun _ : ℤ => Fin 3) _ _
      -- Rewrite the restriction to `n` as a two-step restriction.
      calc
        (intervalMeasure3 a (n + (r + 1))).map
            (Finset.restrict₂ (π := fun _ : ℤ => Fin 3) (Ico_subset_Ico_add a n (r + 1)))
            =
            ((intervalMeasure3 a (n + (r + 1))).map
                (Finset.restrict₂ (π := fun _ : ℤ => Fin 3) (Ico_subset_Ico_succ a (n + r)))).map
              (Finset.restrict₂ (π := fun _ : ℤ => Fin 3) (Ico_subset_Ico_add a n r)) := by
              -- `map_map` with the restriction composition.
              have :
                  (intervalMeasure3 a (n + (r + 1))).map
                      (Finset.restrict₂ (π := fun _ : ℤ => Fin 3)
                        ((Ico_subset_Ico_add a n r).trans (Ico_subset_Ico_succ a (n + r))))
                    =
                    ((intervalMeasure3 a (n + (r + 1))).map
                        (Finset.restrict₂ (π := fun _ : ℤ => Fin 3) (Ico_subset_Ico_succ a (n + r)))).map
                      (Finset.restrict₂ (π := fun _ : ℤ => Fin 3) (Ico_subset_Ico_add a n r)) := by
                    simp [Measure.map_map hmeas₂ hmeas₁, hcomp]
              simpa [Nat.add_assoc, Nat.add_left_comm, Nat.add_comm, hsub'] using this
        _ = (intervalMeasure3 a (n + r)).map
              (Finset.restrict₂ (π := fun _ : ℤ => Fin 3) (Ico_subset_Ico_add a n r)) := by
              simpa [Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using
                congrArg (fun μ => μ.map (Finset.restrict₂ (π := fun _ : ℤ => Fin 3) (Ico_subset_Ico_add a n r)))
                  (intervalMeasure3_map_restrict_snoc (a := a) (n := n + r))
        _ = intervalMeasure3 a n := ih

lemma intervalMeasure3_map_restrict_dropLeft (a : ℤ) (l n : ℕ) :
    (intervalMeasure3 a (n + l)).map
        (Finset.restrict₂ (π := fun _ : ℤ => Fin 3) (Ico_shift_subset_shiftInt a l n))
      = intervalMeasure3 (shiftInt a l) n := by
  classical
  induction l generalizing a with
  | zero =>
      -- `shiftInt a 0 = a` is definitional, so this is just `map_id`.
      have hid :
          Finset.restrict₂ (π := fun _ : ℤ => Fin 3) (Ico_shift_subset_shiftInt a 0 n)
            = (id : (IcoIdx a n → Fin 3) → _) := by
        funext f
        ext i
        rfl
      simp [hid]
  | succ l ih =>
      -- Drop the coordinate at `a`, then apply the inductive hypothesis to drop the next `l`
      -- coordinates.
      let h₁ : IcoIdx (a + 1) (n + l) ⊆ IcoIdx a (n + (l + 1)) := Ico_succ_subset a (n + l)
      let h₂ : IcoIdx (shiftInt (a + 1) l) n ⊆ IcoIdx (a + 1) (n + l) :=
        Ico_shift_subset_shiftInt (a := a + 1) (l := l) (n := n)
      let h₁₂ : IcoIdx (shiftInt (a + 1) l) n ⊆ IcoIdx a (n + (l + 1)) := h₂.trans h₁
      have hgoal :
          Finset.restrict₂ (π := fun _ : ℤ => Fin 3) (Ico_shift_subset_shiftInt a (l + 1) n)
            = Finset.restrict₂ (π := fun _ : ℤ => Fin 3) h₁₂ := by
        exact restrict₂_eq_of_eq (π := fun _ : ℤ => Fin 3) _ _
      have hmeas₁ : Measurable (Finset.restrict₂ (π := fun _ : ℤ => Fin 3) h₁) :=
        Finset.measurable_restrict₂ (X := fun _ : ℤ => Fin 3) h₁
      have hmeas₂ : Measurable (Finset.restrict₂ (π := fun _ : ℤ => Fin 3) h₂) :=
        Finset.measurable_restrict₂ (X := fun _ : ℤ => Fin 3) h₂
      -- `map_map` and the two consistency lemmas.
      calc
        (intervalMeasure3 a (n + (l + 1))).map
            (Finset.restrict₂ (π := fun _ : ℤ => Fin 3) (Ico_shift_subset_shiftInt a (l + 1) n))
            =
            (intervalMeasure3 a (n + (l + 1))).map
              (Finset.restrict₂ (π := fun _ : ℤ => Fin 3) h₁₂) := by
              simp [hgoal]
        _ =
            ((intervalMeasure3 a (n + (l + 1))).map
                (Finset.restrict₂ (π := fun _ : ℤ => Fin 3) h₁)).map
              (Finset.restrict₂ (π := fun _ : ℤ => Fin 3) h₂) := by
              simp [Measure.map_map hmeas₂ hmeas₁, Finset.restrict₂_comp_restrict₂]
        _ =
            (intervalMeasure3 (a + 1) (n + l)).map
              (Finset.restrict₂ (π := fun _ : ℤ => Fin 3) h₂) := by
              simpa using congrArg (fun μ =>
                μ.map (Finset.restrict₂ (π := fun _ : ℤ => Fin 3) h₂))
                (intervalMeasure3_map_restrict_cons (a := a) (n := n + l))
        _ = intervalMeasure3 (shiftInt (a + 1) l) n := by
              simpa [h₂] using (ih (a := a + 1))

lemma intervalMeasure3_map_restrict_subinterval (a : ℤ) (l n r : ℕ) :
    (intervalMeasure3 a (n + l + r)).map
        (Finset.restrict₂ (π := fun _ : ℤ => Fin 3) (Ico_subinterval_subset_shiftInt_right a l n r))
      = intervalMeasure3 (shiftInt a l) n := by
  classical
  -- First drop the last `r` coordinates (keep `n+l`), then drop the first `l` coordinates.
  have hmeas₁ :
      Measurable (Finset.restrict₂ (π := fun _ : ℤ => Fin 3) (Ico_subset_Ico_add a (n + l) r)) :=
    Finset.measurable_restrict₂ (X := fun _ : ℤ => Fin 3) (Ico_subset_Ico_add a (n + l) r)
  have hmeas₂ :
      Measurable (Finset.restrict₂ (π := fun _ : ℤ => Fin 3) (Ico_shift_subset_shiftInt a l n)) :=
    Finset.measurable_restrict₂ (X := fun _ : ℤ => Fin 3) (Ico_shift_subset_shiftInt a l n)
  have hcomp :
      (Finset.restrict₂ (π := fun _ : ℤ => Fin 3) (Ico_shift_subset_shiftInt a l n)) ∘
          (Finset.restrict₂ (π := fun _ : ℤ => Fin 3) (Ico_subset_Ico_add a (n + l) r))
        = Finset.restrict₂ (π := fun _ : ℤ => Fin 3)
            ((Ico_shift_subset_shiftInt a l n).trans (Ico_subset_Ico_add a (n + l) r)) := by
    rfl
  have hsub' :
      Finset.restrict₂ (π := fun _ : ℤ => Fin 3)
          ((Ico_shift_subset_shiftInt a l n).trans (Ico_subset_Ico_add a (n + l) r))
        = Finset.restrict₂ (π := fun _ : ℤ => Fin 3) (Ico_subinterval_subset_shiftInt_right a l n r) := by
    exact restrict₂_eq_of_eq (π := fun _ : ℤ => Fin 3) _ _
  calc
    (intervalMeasure3 a (n + l + r)).map
        (Finset.restrict₂ (π := fun _ : ℤ => Fin 3) (Ico_subinterval_subset_shiftInt_right a l n r))
        =
        ((intervalMeasure3 a (n + l + r)).map
            (Finset.restrict₂ (π := fun _ : ℤ => Fin 3) (Ico_subset_Ico_add a (n + l) r))).map
          (Finset.restrict₂ (π := fun _ : ℤ => Fin 3) (Ico_shift_subset_shiftInt a l n)) := by
          have :
              (intervalMeasure3 a (n + l + r)).map
                  (Finset.restrict₂ (π := fun _ : ℤ => Fin 3)
                    ((Ico_shift_subset_shiftInt a l n).trans (Ico_subset_Ico_add a (n + l) r)))
                =
                ((intervalMeasure3 a (n + l + r)).map
                    (Finset.restrict₂ (π := fun _ : ℤ => Fin 3) (Ico_subset_Ico_add a (n + l) r))).map
                  (Finset.restrict₂ (π := fun _ : ℤ => Fin 3) (Ico_shift_subset_shiftInt a l n)) := by
                simp [Measure.map_map hmeas₂ hmeas₁, hcomp]
          simpa [hsub'] using this
    _ = (intervalMeasure3 a (n + l)).map
          (Finset.restrict₂ (π := fun _ : ℤ => Fin 3) (Ico_shift_subset_shiftInt a l n)) := by
          simpa [Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using
            congrArg (fun μ =>
              μ.map (Finset.restrict₂ (π := fun _ : ℤ => Fin 3) (Ico_shift_subset_shiftInt a l n)))
              (intervalMeasure3_map_restrict_addRight (a := a) (n := n + l) (r := r))
    _ = intervalMeasure3 (shiftInt a l) n := intervalMeasure3_map_restrict_dropLeft (a := a) (l := l) (n := n)

lemma intervalMeasure3_map_restrict_subinterval_of_eq (a : ℤ) (N l n r : ℕ) (hN : N = n + l + r) :
    (intervalMeasure3 a N).map
        (Finset.restrict₂ (π := fun _ : ℤ => Fin 3)
          (by simpa [hN] using Ico_subinterval_subset_shiftInt_right a l n r))
      = intervalMeasure3 (shiftInt a l) n := by
  subst hN
  simpa using (intervalMeasure3_map_restrict_subinterval (a := a) (l := l) (n := n) (r := r))

/-- A version of `intervalMeasure3_map_restrict_subinterval_of_eq` where the subinterval start is
given as an explicit integer `a'`. -/
lemma intervalMeasure3_map_restrict_subinterval_of_eq_start (a a' : ℤ) (N l n r : ℕ)
    (ha : shiftInt a l = a') (hN : N = n + l + r) :
    (intervalMeasure3 a N).map
        (Finset.restrict₂ (π := fun _ : ℤ => Fin 3)
          (by simpa [ha, hN] using Ico_subinterval_subset_shiftInt_right a l n r))
      = intervalMeasure3 a' n := by
  subst hN
  cases ha
  simpa using (intervalMeasure3_map_restrict_subinterval (a := a) (l := l) (n := n) (r := r))

/-! ## The projective family on `Finset ℤ` -/

private lemma add_toNat_sub_eq (a b : ℤ) (h : a ≤ b) : a + ((b - a).toNat : ℤ) = b := by
  have hnonneg : 0 ≤ b - a := sub_nonneg.2 h
  have hz : ((b - a).toNat : ℤ) = b - a := Int.toNat_of_nonneg hnonneg
  calc
    a + ((b - a).toNat : ℤ) = a + (b - a) := by simp [hz]
    _ = b := by abel

/-- The convex hull interval containing a nonempty finset `I`. -/
lemma P3Family_hsub (I : Finset ℤ) (hI : I.Nonempty) :
    I ⊆ IcoIdx (I.min' hI) ((I.max' hI + 1 - I.min' hI).toNat) := by
  intro x hx
  have hmin : I.min' hI ≤ x := I.min'_le x hx
  have hmax : x ≤ I.max' hI := I.le_max' x hx
  have hxlt : x < I.max' hI + 1 := lt_of_le_of_lt hmax (lt_add_one _)
  have hab : I.min' hI + ((I.max' hI + 1 - I.min' hI).toNat : ℤ) = I.max' hI + 1 := by
    have : I.min' hI ≤ I.max' hI + 1 := by
      have : I.min' hI ≤ I.max' hI := I.min'_le (I.max' hI) (I.max'_mem hI)
      linarith
    simpa using add_toNat_sub_eq (I.min' hI) (I.max' hI + 1) this
  refine (Finset.mem_Ico).2 ?_
  constructor
  · exact hmin
  · exact lt_of_lt_of_eq hxlt hab.symm

noncomputable def P3Family (I : Finset ℤ) : Measure (I → Fin 3) :=
  if hI : I.Nonempty then
    (intervalMeasure3 (I.min' hI) ((I.max' hI + 1 - I.min' hI).toNat)).map
      (Finset.restrict₂ (π := fun _ : ℤ => Fin 3) (P3Family_hsub I hI))
  else
    Measure.dirac (fun _ : I => (0 : Fin 3))

lemma P3Family_empty : P3Family (∅ : Finset ℤ) = Measure.dirac (fun _ : (∅ : Finset ℤ) => (0 : Fin 3)) := by
  simp [P3Family]

theorem P3Family_projective :
    MeasureTheory.IsProjectiveMeasureFamily (ι := ℤ) (α := fun _ : ℤ => Fin 3)
      (fun I : Finset ℤ => P3Family I) := by
  classical
  intro I J hJI
  -- Unfold the projective-family goal so later rewrites match syntactically.
  change
      P3Family J =
        (P3Family I).map (Finset.restrict₂ (π := fun _ : ℤ => Fin 3) hJI)
  by_cases hJ : J.Nonempty
  · have hI : I.Nonempty := Finset.Nonempty.mono hJI hJ
    -- Names for the interval hulls of `I` and `J`.
    set aI : ℤ := I.min' hI with haI
    set bI : ℤ := I.max' hI + 1 with hbI
    set nI : ℕ := (bI - aI).toNat with hnI
    set aJ : ℤ := J.min' hJ with haJ
    set bJ : ℤ := J.max' hJ + 1 with hbJ
    -- Define `nJ` without reference to `aJ`, to keep later rewrites simpler.
    set nJ : ℕ := (bJ - J.min' hJ).toNat with hnJ

    have haI_le_aJ : aI ≤ aJ := by
      have haJ_memJ : aJ ∈ J := by simpa [haJ] using J.min'_mem hJ
      have haJ_memI : aJ ∈ I := hJI haJ_memJ
      simpa [haI] using I.min'_le aJ haJ_memI

    have hbJ_le_bI : bJ ≤ bI := by
      have hmaxJ_memJ : J.max' hJ ∈ J := J.max'_mem hJ
      have hmaxJ_memI : J.max' hJ ∈ I := hJI hmaxJ_memJ
      have hmaxJ_le_maxI : J.max' hJ ≤ I.max' hI := I.le_max' (J.max' hJ) hmaxJ_memI
      have : J.max' hJ + 1 ≤ I.max' hI + 1 := add_le_add_left hmaxJ_le_maxI 1
      simpa [hbJ, hbI] using this

    -- Offsets locating the `J`-hull inside the `I`-hull.
    -- Define `l` without reference to `aJ`, to keep later rewrites simpler.
    set l : ℕ := (J.min' hJ - aI).toNat with hl_def
    set r : ℕ := (bI - bJ).toNat with hr_def

    have haJ_eq : aJ = shiftInt aI l := by
      -- `shiftInt aI l = aI + l = aJ`.
      have : shiftInt aI l = aJ := by
        calc
          shiftInt aI l = aI + l := by simpa using (shiftInt_eq_add aI l)
          _ = aJ := by
                have hle : aI ≤ J.min' hJ := by
                  simpa [haJ] using haI_le_aJ
                -- `aI + ((J.min' hJ - aI).toNat : ℤ) = J.min' hJ = aJ`.
                have : aI + ((J.min' hJ - aI).toNat : ℤ) = J.min' hJ := add_toNat_sub_eq aI (J.min' hJ) hle
                simpa [hl_def, haJ] using this
      exact this.symm

    have hN : nI = nJ + l + r := by
      -- compare in `ℤ` and use `Int.ofNat.inj`.
      apply Int.ofNat.inj
      have haI_le_bI : aI ≤ bI := by
        have : I.min' hI ≤ I.max' hI + 1 := by
          have : I.min' hI ≤ I.max' hI := I.min'_le (I.max' hI) (I.max'_mem hI)
          linarith
        simpa [haI, hbI] using this
      have haJ_le_bJ : aJ ≤ bJ := by
        have : J.min' hJ ≤ J.max' hJ + 1 := by
          have : J.min' hJ ≤ J.max' hJ := J.min'_le (J.max' hJ) (J.max'_mem hJ)
          linarith
        simpa [haJ, hbJ] using this
      have hnI : (nI : ℤ) = bI - aI := by
        have hnonneg : 0 ≤ bI - aI := sub_nonneg.2 haI_le_bI
        simpa [hnI] using (Int.toNat_of_nonneg hnonneg)
      have hnJ : (nJ : ℤ) = bJ - J.min' hJ := by
        have hmin_le : J.min' hJ ≤ bJ := by simpa [haJ] using haJ_le_bJ
        have hnonneg : 0 ≤ bJ - J.min' hJ := sub_nonneg.2 hmin_le
        simpa [hnJ] using (Int.toNat_of_nonneg hnonneg)
      have hl : (l : ℤ) = aJ - aI := by
        have hle : aI ≤ J.min' hJ := by
          simpa [haJ] using haI_le_aJ
        have hnonneg : 0 ≤ J.min' hJ - aI := sub_nonneg.2 hle
        -- rewrite `J.min' hJ` back to `aJ`.
        simpa [hl_def, haJ] using (Int.toNat_of_nonneg hnonneg)
      have hr : (r : ℤ) = bI - bJ := by
        have hnonneg : 0 ≤ bI - bJ := sub_nonneg.2 hbJ_le_bI
        simpa [hr_def] using (Int.toNat_of_nonneg hnonneg)
      -- Now compute both sides as integers.
      have : (nI : ℤ) = (nJ + l + r : ℤ) := by
        calc
          (nI : ℤ) = bI - aI := hnI
          _ = (bI - bJ) + (bJ - aJ) + (aJ - aI) := by abel
              _ = (r : ℤ) + (nJ : ℤ) + (l : ℤ) := by
                    simp [hnJ, haJ, hl, hr]
          _ = (nJ + l + r : ℤ) := by
                simp [add_left_comm, add_comm]
      simpa using this

    have hsubI : I ⊆ IcoIdx aI nI := by
      -- this is exactly `P3Family_hsub I hI`, rewritten through the abbreviations.
      simpa [haI, hbI, hnI] using (P3Family_hsub I hI)
    have hsubJ : J ⊆ IcoIdx aJ nJ := by
      simpa [haJ, hbJ, hnJ] using (P3Family_hsub J hJ)

    -- Rewrite both sides of the projectivity statement.
    have hPI : P3Family I =
        (intervalMeasure3 aI nI).map (Finset.restrict₂ (π := fun _ : ℤ => Fin 3) hsubI) := by
      have hnI' : (I.max' hI + 1 - I.min' hI).toNat = nI := by
        simpa [hbI, haI] using hnI.symm
      have hsubI' : I ⊆ IcoIdx (I.min' hI) ((I.max' hI + 1 - I.min' hI).toNat) := by
        simpa [haI, hnI'.symm] using hsubI
      have hEq :
          (Finset.restrict₂ (π := fun _ : ℤ => Fin 3) (P3Family_hsub I hI))
            = Finset.restrict₂ (π := fun _ : ℤ => Fin 3) hsubI' := by
        exact restrict₂_eq_of_eq (π := fun _ : ℤ => Fin 3) _ _
      have :
          P3Family I =
            (intervalMeasure3 (I.min' hI) ((I.max' hI + 1 - I.min' hI).toNat)).map
              (Finset.restrict₂ (π := fun _ : ℤ => Fin 3) hsubI') := by
        simp [P3Family, hI, hEq]
      simpa [haI, hnI'.symm] using this

    have hPJ : P3Family J =
        (intervalMeasure3 aJ nJ).map (Finset.restrict₂ (π := fun _ : ℤ => Fin 3) hsubJ) := by
      have hnJ' : (J.max' hJ + 1 - J.min' hJ).toNat = nJ := by
        simpa [hbJ, haJ] using hnJ.symm
      have hsubJ' : J ⊆ IcoIdx (J.min' hJ) ((J.max' hJ + 1 - J.min' hJ).toNat) := by
        simpa [haJ, hnJ'.symm] using hsubJ
      have hEq :
          (Finset.restrict₂ (π := fun _ : ℤ => Fin 3) (P3Family_hsub J hJ))
            = Finset.restrict₂ (π := fun _ : ℤ => Fin 3) hsubJ' := by
        exact restrict₂_eq_of_eq (π := fun _ : ℤ => Fin 3) _ _
      have :
          P3Family J =
            (intervalMeasure3 (J.min' hJ) ((J.max' hJ + 1 - J.min' hJ).toNat)).map
              (Finset.restrict₂ (π := fun _ : ℤ => Fin 3) hsubJ') := by
        simp [P3Family, hJ, hEq]
      simpa [haJ, hnJ'.symm] using this

    -- The inclusion of the `J`-hull into the `I`-hull.
    have hHull : IcoIdx aJ nJ ⊆ IcoIdx aI nI := by
      -- `Ico_subinterval_subset_shiftInt_right` gives the inclusion into length `nJ+l+r`.
      simpa [haJ_eq.symm, hN] using
        (Ico_subinterval_subset_shiftInt_right (a := aI) (l := l) (n := nJ) (r := r))

    have hHull_measure :
        (intervalMeasure3 aI nI).map
            (Finset.restrict₂ (π := fun _ : ℤ => Fin 3) hHull)
          = intervalMeasure3 aJ nJ := by
      -- Apply the subinterval consistency lemma directly (with start `aJ`).
      have hcanon : IcoIdx aJ nJ ⊆ IcoIdx aI nI := by
        simpa [haJ_eq.symm, hN] using
          (Ico_subinterval_subset_shiftInt_right (a := aI) (l := l) (n := nJ) (r := r))
      have hcanon_measure :
          (intervalMeasure3 aI nI).map
              (Finset.restrict₂ (π := fun _ : ℤ => Fin 3) hcanon)
            = intervalMeasure3 aJ nJ := by
        simpa using
          (intervalMeasure3_map_restrict_subinterval_of_eq_start (a := aI) (a' := aJ) (N := nI)
            (l := l) (n := nJ) (r := r) haJ_eq.symm hN)
      have hre :
          (Finset.restrict₂ (π := fun _ : ℤ => Fin 3) hHull) =
            (Finset.restrict₂ (π := fun _ : ℤ => Fin 3) hcanon) := by
        exact restrict₂_eq_of_eq (π := fun _ : ℤ => Fin 3) hHull hcanon
      simpa [hre] using hcanon_measure

    -- Now unfold `P3Family` and use `map_map` plus `hHull_measure`.
    have hmeasJI : Measurable (Finset.restrict₂ (π := fun _ : ℤ => Fin 3) hJI) :=
      Finset.measurable_restrict₂ (X := fun _ : ℤ => Fin 3) hJI
    have hmeasI : Measurable (Finset.restrict₂ (π := fun _ : ℤ => Fin 3) hsubI) :=
      Finset.measurable_restrict₂ (X := fun _ : ℤ => Fin 3) hsubI
    have hmeasJ : Measurable (Finset.restrict₂ (π := fun _ : ℤ => Fin 3) hsubJ) :=
      Finset.measurable_restrict₂ (X := fun _ : ℤ => Fin 3) hsubJ
    have hmeasHull : Measurable (Finset.restrict₂ (π := fun _ : ℤ => Fin 3) hHull) :=
      Finset.measurable_restrict₂ (X := fun _ : ℤ => Fin 3) hHull

    have hsubEq :
        Finset.restrict₂ (π := fun _ : ℤ => Fin 3) (hJI.trans hsubI) =
          Finset.restrict₂ (π := fun _ : ℤ => Fin 3) (hsubJ.trans hHull) := by
      exact restrict₂_eq_of_eq (π := fun _ : ℤ => Fin 3) _ _

    -- `IsProjectiveMeasureFamily` asks for the identity `P3Family J = (P3Family I).map ...`.
    rw [hPJ, hPI]
    -- Rewrite the two-step restriction `hsubI` then `hJI` as a single restriction from the `I`-hull to `J`.
    simp [Measure.map_map hmeasJI hmeasI, Finset.restrict₂_comp_restrict₂]
    -- Replace the one-step restriction by the two-step restriction through the hull of `J`.
    simp only [hsubEq]
    -- Apply `map_map` and the hull restriction lemma.
    have :
        (intervalMeasure3 aI nI).map (Finset.restrict₂ (π := fun _ : ℤ => Fin 3) (hsubJ.trans hHull))
          =
          ((intervalMeasure3 aI nI).map (Finset.restrict₂ (π := fun _ : ℤ => Fin 3) hHull)).map
            (Finset.restrict₂ (π := fun _ : ℤ => Fin 3) hsubJ) := by
      simp [Measure.map_map hmeasJ hmeasHull, Finset.restrict₂_comp_restrict₂]
    rw [this, hHull_measure]
  · -- `J` is empty.
    have hJ' : J = ∅ := Finset.not_nonempty_iff_eq_empty.mp hJ
    subst hJ'
    -- Restricting any measure to the empty set of indices is a constant map, hence a dirac measure.
    have hconst :
        (Finset.restrict₂ (π := fun _ : ℤ => Fin 3) (Finset.empty_subset I)) =
          (fun _ : (I → Fin 3) => (fun _ : (∅ : Finset ℤ) => (0 : Fin 3))) := by
      funext x
      exact Subsingleton.elim _ _
    have h_univ : (P3Family I) univ = 1 := by
      classical
      by_cases hI : I.Nonempty
      · have hmeas_restrict :
            Measurable (Finset.restrict₂ (π := fun _ : ℤ => Fin 3) (P3Family_hsub I hI)) :=
          Finset.measurable_restrict₂ (X := fun _ : ℤ => Fin 3) (P3Family_hsub I hI)
        have hmeas_word :
            Measurable (wordToIco (q := 3) (I.min' hI) ((I.max' hI + 1 - I.min' hI).toNat)) := by
          simpa using
            measurable_of_finite (wordToIco (q := 3) (I.min' hI) ((I.max' hI + 1 - I.min' hI).toNat))
        -- `intervalMeasure3` and `P3Family` are probability measures.
        simp [P3Family, hI, intervalMeasure3, Measure.map_apply, hmeas_restrict, hmeas_word]
      · simp [P3Family, hI]
    -- Now evaluate the map along the constant function.
    have hmap :
        (P3Family I).map (Finset.restrict₂ (π := fun _ : ℤ => Fin 3) (Finset.empty_subset I))
          =
          ((P3Family I) univ) • Measure.dirac (fun _ : (∅ : Finset ℤ) => (0 : Fin 3)) := by
      simp [hconst]
    simp [P3Family_empty, hmap, h_univ]

/-! ## Additive content and projective limit measure -/

private lemma isOpen_of_mem_measurableCylinders {s : Set (ℤ → Fin 3)}
    (hs : s ∈ measurableCylinders (fun _ : ℤ => Fin 3)) : IsOpen s := by
  rcases (mem_measurableCylinders _).1 hs with ⟨I, S, _hSmeas, rfl⟩
  have hSopen : IsOpen S := isOpen_discrete S
  simpa [cylinder] using hSopen.preimage (Finset.continuous_restrict (A := fun _ : ℤ => Fin 3) I)

private lemma isCompact_of_mem_measurableCylinders {s : Set (ℤ → Fin 3)}
    (hs : s ∈ measurableCylinders (fun _ : ℤ => Fin 3)) : IsCompact s := by
  rcases (mem_measurableCylinders _).1 hs with ⟨I, S, _hSmeas, rfl⟩
  have hSclosed : IsClosed S := isClosed_discrete S
  have hclosed : IsClosed (cylinder I S : Set (ℤ → Fin 3)) := by
    simpa [cylinder] using hSclosed.preimage (Finset.continuous_restrict (A := fun _ : ℤ => Fin 3) I)
  exact hclosed.isCompact

noncomputable def μ3Content :
    MeasureTheory.AddContent ℝ≥0∞ (measurableCylinders (fun _ : ℤ => Fin 3)) :=
  projectiveFamilyContent (α := fun _ : ℤ => Fin 3) (mα := fun _ : ℤ => inferInstance)
    P3Family_projective

lemma μ3Content_isSigmaSubadditive : μ3Content.IsSigmaSubadditive := by
  classical
  intro f hf hU
  -- Let `s = ⋃ n, f n`. It is a measurable cylinder, hence compact.
  have hs_compact : IsCompact (⋃ n, f n) := isCompact_of_mem_measurableCylinders (hs := hU)
  have hUopen : ∀ n, IsOpen (f n) := fun n => isOpen_of_mem_measurableCylinders (hs := hf n)
  -- Extract a finite subcover.
  rcases hs_compact.elim_finite_subcover f hUopen (by simp) with ⟨t, ht⟩
  -- Use monotonicity and finite subadditivity on `t`.
  have h_union_mem : (⋃ i ∈ t, f i) ∈ measurableCylinders (fun _ : ℤ => Fin 3) := by
    -- `measurableCylinders` is a set algebra.
    have hAlg :=
        MeasureTheory.isSetAlgebra_measurableCylinders (α := fun _ : ℤ => Fin 3)
          (mα := fun _ : ℤ => inferInstance)
    refine Finset.induction_on t ?_ ?_
    · simpa [Set.iUnion_false] using (empty_mem_measurableCylinders (fun _ : ℤ => Fin 3))
    · intro i t hit ih
      simp only [Finset.mem_insert] at *
      -- union of two cylinders
      have hi : f i ∈ measurableCylinders (fun _ : ℤ => Fin 3) := hf i
      have ht' : (⋃ j ∈ t, f j) ∈ measurableCylinders (fun _ : ℤ => Fin 3) := ih
      simpa [Set.biUnion_insert] using hAlg.union_mem hi ht'
  have h_le_cover :
      μ3Content (⋃ n, f n) ≤ μ3Content (⋃ i ∈ t, f i) := by
    exact projectiveFamilyContent_mono (hP := P3Family_projective) hU h_union_mem ht
  have h_le_sum :
      μ3Content (⋃ i ∈ t, f i) ≤ ∑ i ∈ t, μ3Content (f i) := by
    -- finite subadditivity for an additive content on a ring of sets
    simpa using addContent_biUnion_le (m := μ3Content)
      (hC := MeasureTheory.isSetRing_measurableCylinders (α := fun _ : ℤ => Fin 3)
        (mα := fun _ : ℤ => inferInstance)) (s := f) (S := t) (fun i _ => hf i)
  have h_sum_le : (∑ i ∈ t, μ3Content (f i)) ≤ ∑' i, μ3Content (f i) := by
    simpa using (ENNReal.sum_le_tsum (s := t) (f := fun i => μ3Content (f i)))
  exact le_trans (le_trans h_le_cover h_le_sum) h_sum_le

lemma μ3Measure_generateFrom :
    (MeasurableSpace.pi : MeasurableSpace (ℤ → Fin 3))
      = MeasurableSpace.generateFrom (measurableCylinders (fun _ : ℤ => Fin 3)) := by
  simpa using (generateFrom_measurableCylinders (α := fun _ : ℤ => Fin 3)).symm

noncomputable def μ3Measure : Measure (ℤ → Fin 3) :=
  μ3Content.measure (hC := MeasureTheory.isSetSemiring_measurableCylinders (α := fun _ : ℤ => Fin 3)
      (mα := fun _ : ℤ => inferInstance))
    (hC_gen := μ3Measure_generateFrom.le) (m_sigma_subadd := μ3Content_isSigmaSubadditive)

noncomputable def μ3 : ProbabilityMeasure (ℤ → Fin 3) :=
  ⟨μ3Measure, by
    classical
    have hμ_univ : μ3Measure univ = μ3Content univ := by
      have : univ ∈ measurableCylinders (fun _ : ℤ => Fin 3) :=
        univ_mem_measurableCylinders (fun _ : ℤ => Fin 3)
      simp [μ3Measure, MeasureTheory.AddContent.measure_eq (m := μ3Content)
        (hC := MeasureTheory.isSetSemiring_measurableCylinders (α := fun _ : ℤ => Fin 3)
          (mα := fun _ : ℤ => inferInstance))
        (hC_gen := μ3Measure_generateFrom) (m_sigma_subadd := μ3Content_isSigmaSubadditive), this]
    have hm_univ : μ3Content univ = 1 := by
      -- `univ` is `cylinder ∅ univ`.
      have huniv :
          (univ : Set (ℤ → Fin 3)) =
            cylinder (∅ : Finset ℤ) (univ : Set ((∅ : Finset ℤ) → Fin 3)) := by
        simp
      calc
        μ3Content univ =
            μ3Content (cylinder (∅ : Finset ℤ) (univ : Set ((∅ : Finset ℤ) → Fin 3))) := by
              exact congrArg μ3Content huniv
        _ = P3Family (∅ : Finset ℤ) (univ : Set ((∅ : Finset ℤ) → Fin 3)) := by
              simpa [μ3Content] using
                (projectiveFamilyContent_cylinder (hP := P3Family_projective) (I := (∅ : Finset ℤ))
                  (S := (univ : Set ((∅ : Finset ℤ) → Fin 3))) MeasurableSet.univ)
        _ = 1 := by
              simp [P3Family_empty]
    have : μ3Measure univ = 1 := by simp [hμ_univ, hm_univ]
    exact ⟨this⟩⟩

end Word

end FiniteDependence.Coloring
