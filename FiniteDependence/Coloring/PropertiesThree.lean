import FiniteDependence.Coloring.ProcessThree
import Mathlib.MeasureTheory.Measure.Typeclasses.Finite

/-!
# Properties of the `q = 3` two-sided process

This file proves that the probability measure `Word.μ3` constructed from the projective family
`Word.P3Family` is stationary (shift-invariant), and that it is almost surely a proper coloring of
`ℤ`.
-/

open scoped ENNReal BigOperators

namespace FiniteDependence.Coloring

namespace Word

open MeasureTheory Set

namespace Three

/-! ## Shift on finite index sets -/

/-- Shift a finite set of indices by `+1`. -/
noncomputable def shiftFinset (I : Finset ℤ) : Finset ℤ :=
  I.image (fun z : ℤ => z + 1)

/-- The shifted element `i ↦ i+1` as a map `I → shiftFinset I`. -/
noncomputable def shiftElem (I : Finset ℤ) (i : I) : shiftFinset I := by
  refine ⟨i.1 + 1, ?_⟩
  classical
  exact Finset.mem_image.2 ⟨i.1, i.2, rfl⟩

/-- Precompose an assignment on `shiftFinset I` by the shift map `i ↦ i+1`. -/
noncomputable def precompShiftFinset (I : Finset ℤ) :
    (shiftFinset I → Fin 3) → (I → Fin 3) :=
  fun f i => f (shiftElem I i)

lemma shiftFinset_nonempty {I : Finset ℤ} (hI : I.Nonempty) : (shiftFinset I).Nonempty :=
  hI.image (fun z : ℤ => z + 1)

lemma measurable_precompShiftFinset (I : Finset ℤ) : Measurable (precompShiftFinset I) := by
  classical
  simpa using measurable_of_finite (precompShiftFinset I)

lemma measurable_shift : Measurable (FiniteDependence.Coloring.shift (q := 3)) := by
  simpa [FiniteDependence.Coloring.shift] using (FiniteDependence.measurable_shift (α := Fin 3))

/-! ## Cylinders and shift -/

lemma restrict_shift_eq_precomp (I : Finset ℤ) (x : ℤ → Fin 3) :
    I.restrict (FiniteDependence.Coloring.shift (q := 3) x)
      = precompShiftFinset I ((shiftFinset I).restrict x) := by
  funext i
  rfl

lemma preimage_shift_cylinder (I : Finset ℤ) (S : Set (I → Fin 3)) :
    (FiniteDependence.Coloring.shift (q := 3)) ⁻¹' (cylinder I S)
      = cylinder (shiftFinset I) ((precompShiftFinset I) ⁻¹' S) := by
  ext x
  simp [cylinder, restrict_shift_eq_precomp]

/-! ## Shift invariance of `P3Family` -/

private lemma monotone_add_one : Monotone (fun z : ℤ => z + 1) := by
  intro a b hab
  exact add_le_add_left hab 1

lemma min'_shiftFinset {I : Finset ℤ} (hI : I.Nonempty) :
    (shiftFinset I).min' (shiftFinset_nonempty (I := I) hI) = I.min' hI + 1 := by
  simpa [shiftFinset, shiftFinset_nonempty] using
    (Monotone.map_finset_min' (α := ℤ) (β := ℤ) monotone_add_one (s := I) hI).symm

lemma max'_shiftFinset {I : Finset ℤ} (hI : I.Nonempty) :
    (shiftFinset I).max' (shiftFinset_nonempty (I := I) hI) = I.max' hI + 1 := by
  simpa [shiftFinset, shiftFinset_nonempty] using
    (Monotone.map_finset_max' (α := ℤ) (β := ℤ) monotone_add_one (s := I) hI).symm

/-- `P3Family` is equivariant under shifting indices by `+1`. -/
lemma P3Family_map_precompShiftFinset (I : Finset ℤ) :
    (P3Family (shiftFinset I)).map (precompShiftFinset I) = P3Family I := by
  classical
  by_cases hI : I.Nonempty
  ·
    -- A non-emptiness witness for the shifted finset.
    have hI' : (shiftFinset I).Nonempty := shiftFinset_nonempty (I := I) hI

    -- Shorthand for the hull interval parameters of `I`.
    set a : ℤ := I.min' hI with ha
    set n : ℕ := (I.max' hI + 1 - I.min' hI).toNat with hn

    -- Hull parameters for `shiftFinset I` (as variables, so we can substitute them later).
    generalize haS : (shiftFinset I).min' hI' = aS
    generalize hnS : ((shiftFinset I).max' hI' + 1 - aS).toNat = nS
    have hsubS : shiftFinset I ⊆ IcoIdx aS nS := by
      simpa [haS, hnS] using (P3Family_hsub (I := shiftFinset I) hI')

    have hmeas_pre : Measurable (precompShiftFinset I) := measurable_precompShiftFinset I

    have hPshift :
        P3Family (shiftFinset I) =
          (intervalMeasure3 aS nS).map (Finset.restrict₂ (π := fun _ : ℤ => Fin 3) hsubS) := by
      cases haS
      cases hnS
      have hre :
          (Finset.restrict₂ (π := fun _ : ℤ => Fin 3) (P3Family_hsub (I := shiftFinset I) hI'))
            = Finset.restrict₂ (π := fun _ : ℤ => Fin 3) hsubS := by
        exact restrict₂_eq_of_eq (π := fun _ : ℤ => Fin 3) _ _
      simp [P3Family, hI', hre]

    -- Convert the shift-hull parameters `(aS, nS)` to `(a+1, n)`.
    have haS' : aS = a + 1 := by
      calc
        aS = (shiftFinset I).min' hI' := by simpa using haS.symm
        _ = I.min' hI + 1 := by
              simpa [shiftFinset_nonempty] using (min'_shiftFinset (I := I) hI)
        _ = a + 1 := by simp [a]
    subst haS'

    have hnS' : nS = n := by
      have hmaxS : (shiftFinset I).max' hI' = I.max' hI + 1 := by
        simpa [shiftFinset_nonempty] using (max'_shiftFinset (I := I) hI)
      have hadd :
          (I.max' hI + 1 + 1 - (I.min' hI + 1) : ℤ) = I.max' hI + 1 - I.min' hI := by
        abel
      subst n
      have : nS = ((shiftFinset I).max' hI' + 1 - (a + 1)).toNat := by
        simpa using hnS.symm
      simp [this, hmaxS, a, hadd]
    subst hnS'

    have hmeas_preico : Measurable (precompShiftIcoIdx3 a n) := by
      simpa [a, n] using measurable_of_finite (precompShiftIcoIdx3 a n)
    have hmeas_res_I :
        Measurable (Finset.restrict₂ (π := fun _ : ℤ => Fin 3) (P3Family_hsub (I := I) hI)) := by
      simpa using
        (Finset.measurable_restrict₂ (X := fun _ : ℤ => Fin 3) (P3Family_hsub (I := I) hI))
    have hmeas_res_shift :
        Measurable (Finset.restrict₂ (π := fun _ : ℤ => Fin 3) hsubS) := by
      simpa using (Finset.measurable_restrict₂ (X := fun _ : ℤ => Fin 3) hsubS)

    have hcomp :
        (precompShiftFinset I) ∘ (Finset.restrict₂ (π := fun _ : ℤ => Fin 3) hsubS)
          = (Finset.restrict₂ (π := fun _ : ℤ => Fin 3) (P3Family_hsub (I := I) hI)) ∘
              precompShiftIcoIdx3 a n := by
      funext f
      funext i
      rfl

    calc
      (P3Family (shiftFinset I)).map (precompShiftFinset I)
          = ((intervalMeasure3 (a + 1) n).map
              (Finset.restrict₂ (π := fun _ : ℤ => Fin 3) hsubS)).map (precompShiftFinset I) := by
              simp [hPshift]
      _ = (intervalMeasure3 (a + 1) n).map
            ((precompShiftFinset I) ∘ (Finset.restrict₂ (π := fun _ : ℤ => Fin 3) hsubS)) := by
              simp [Measure.map_map hmeas_pre hmeas_res_shift]
      _ = (intervalMeasure3 (a + 1) n).map
            ((Finset.restrict₂ (π := fun _ : ℤ => Fin 3) (P3Family_hsub (I := I) hI)) ∘
              precompShiftIcoIdx3 a n) := by
              simp [hcomp]
      _ = ((intervalMeasure3 (a + 1) n).map (precompShiftIcoIdx3 a n)).map
            (Finset.restrict₂ (π := fun _ : ℤ => Fin 3) (P3Family_hsub (I := I) hI)) := by
              simp [Measure.map_map hmeas_res_I hmeas_preico]
      _ = (intervalMeasure3 a n).map
            (Finset.restrict₂ (π := fun _ : ℤ => Fin 3) (P3Family_hsub (I := I) hI)) := by
              simp [intervalMeasure3_map_precompShiftIcoIdx3]
      _ = P3Family I := by
              simp [P3Family, hI, a, n]
  ·
    have hI' : I = ∅ := Finset.not_nonempty_iff_eq_empty.1 hI
    subst hI'
    have hmeas : Measurable (precompShiftFinset (∅ : Finset ℤ)) :=
      measurable_precompShiftFinset (∅ : Finset ℤ)
    have hfun :
        precompShiftFinset (∅ : Finset ℤ) (fun _ : shiftFinset (∅ : Finset ℤ) => (0 : Fin 3))
          = (fun _ : (∅ : Finset ℤ) => (0 : Fin 3)) := by
      funext i
      cases i with
      | mk x hx =>
        simp at hx
    have hmap :
        (P3Family (shiftFinset (∅ : Finset ℤ))).map (precompShiftFinset (∅ : Finset ℤ))
          =
          Measure.dirac
            (precompShiftFinset (∅ : Finset ℤ)
              (fun _ : shiftFinset (∅ : Finset ℤ) => (0 : Fin 3))) := by
      have hempty : ¬(shiftFinset (∅ : Finset ℤ)).Nonempty := by
        simp [shiftFinset]
      simp [P3Family, hempty, Measure.map_dirac hmeas]
    simpa [P3Family, shiftFinset, hfun] using hmap

end Three

/-! ## Stationarity of `μ3` -/

theorem μ3_isStationary : IsStationary (q := 3) μ3 := by
  classical
  change (μ3Measure.map (FiniteDependence.Coloring.shift (q := 3))) = μ3Measure
  letI : MeasureTheory.IsFiniteMeasure (μ3Measure.map (FiniteDependence.Coloring.shift (q := 3))) :=
    MeasureTheory.IsFiniteMeasure.mk (by
      have hμ_univ : μ3Measure univ = (1 : ℝ≥0∞) := by
        simpa [μ3] using
          (MeasureTheory.IsProbabilityMeasure.measure_univ (μ := (μ3 : Measure (ℤ → Fin 3))))
      have hmap_univ :
          μ3Measure.map (FiniteDependence.Coloring.shift (q := 3)) univ = (1 : ℝ≥0∞) := by
        simp [Measure.map_apply Three.measurable_shift MeasurableSet.univ, hμ_univ]
      simp [hmap_univ])

  refine MeasureTheory.ext_of_generate_finite (μ := μ3Measure.map (FiniteDependence.Coloring.shift (q := 3)))
    (ν := μ3Measure) (C := measurableCylinders (fun _ : ℤ => Fin 3)) ?_ ?_ ?_ ?_
  · simpa using μ3Measure_generateFrom
  · simpa using (MeasureTheory.isPiSystem_measurableCylinders (α := fun _ : ℤ => Fin 3))
  · intro s hs
    rcases (mem_measurableCylinders _).1 hs with ⟨I, S, hS, rfl⟩
    have hmeas_cyl : MeasurableSet (cylinder I S : Set (ℤ → Fin 3)) := by
      have hmeas_restrict : Measurable (I.restrict : (ℤ → Fin 3) → I → Fin 3) :=
        measurable_pi_lambda _ (fun _ => measurable_pi_apply _)
      simpa [cylinder] using hS.preimage hmeas_restrict
    have :
        μ3Measure.map (FiniteDependence.Coloring.shift (q := 3)) (cylinder I S : Set (ℤ → Fin 3))
          = μ3Measure (cylinder I S : Set (ℤ → Fin 3)) := by
      have hmap :
          μ3Measure.map (FiniteDependence.Coloring.shift (q := 3)) (cylinder I S : Set (ℤ → Fin 3))
            = μ3Measure ((FiniteDependence.Coloring.shift (q := 3)) ⁻¹' (cylinder I S)) := by
        simp [Measure.map_apply Three.measurable_shift hmeas_cyl]
      rw [hmap, Three.preimage_shift_cylinder (I := I) (S := S)]
      have hS' : MeasurableSet ((Three.precompShiftFinset I) ⁻¹' S) :=
        (Three.measurable_precompShiftFinset I) hS
      have hmeas_precomp : Measurable (Three.precompShiftFinset I) :=
        Three.measurable_precompShiftFinset I
      calc
        μ3Measure
            (cylinder (Three.shiftFinset I) ((Three.precompShiftFinset I) ⁻¹' S) : Set (ℤ → Fin 3))
            = P3Family (Three.shiftFinset I) ((Three.precompShiftFinset I) ⁻¹' S) := by
                exact μ3Measure_cylinder (I := Three.shiftFinset I)
                  (S := (Three.precompShiftFinset I ⁻¹' S)) hS'
        _ = ((P3Family (Three.shiftFinset I)).map (Three.precompShiftFinset I)) S := by
              simp [Measure.map_apply hmeas_precomp hS]
        _ = P3Family I S := by
              simpa using congrArg (fun μ =>
                μ S) (Three.P3Family_map_precompShiftFinset (I := I))
        _ = μ3Measure (cylinder I S : Set (ℤ → Fin 3)) := by
              exact (μ3Measure_cylinder (I := I) (S := S) hS).symm
    simpa using this
  · simp [Measure.map_apply Three.measurable_shift MeasurableSet.univ]

/-! ## Proper coloring almost surely -/

namespace Three

/-- The index `i` inside `IcoIdx i 2` corresponding to `0 : Fin 2`. -/
noncomputable def icoIdx0 (i : ℤ) : IcoIdx i 2 :=
  (equivIco i 2) (0 : Fin 2)

/-- The index `i+1` inside `IcoIdx i 2` corresponding to `1 : Fin 2`. -/
noncomputable def icoIdx1 (i : ℤ) : IcoIdx i 2 :=
  (equivIco i 2) (1 : Fin 2)

/-- Words of length `2` with equal adjacent letters. -/
def eq01Set : Set (Word 3 2) :=
  {w | w (0 : Fin 2) = w (1 : Fin 2)}

/-- Interval assignments on `[i, i+2)` with equal adjacent values. -/
def adjEqSet (i : ℤ) : Set (IcoIdx i 2 → Fin 3) :=
  {f | f (icoIdx0 i) = f (icoIdx1 i)}

lemma measurableSet_eq01Set : MeasurableSet (eq01Set) := by
  classical
  have h0 : Measurable (fun w : Word 3 2 => w (0 : Fin 2)) := by
    simpa using (measurable_pi_apply (a := (0 : Fin 2)))
  have h1 : Measurable (fun w : Word 3 2 => w (1 : Fin 2)) := by
    simpa using (measurable_pi_apply (a := (1 : Fin 2)))
  simpa [eq01Set] using measurableSet_eq_fun h0 h1

lemma P3_two_eq_zero_of_mem_eq01Set {w : Word 3 2} (hw : w ∈ eq01Set) : P3 2 w = 0 := by
  have h : w (0 : Fin 2) = w (1 : Fin 2) := hw
  have hnot : ¬ IsProper w := by
    simpa [IsProper] using h
  have hB : B (q := 3) w = 0 := by
    simpa using (B_eq_zero_of_not_isProper (q := 3) (x := w) (n := 1) hnot)
  simp [P3, hB]

lemma pmf3_two_toMeasure_eq01Set : (pmf3 2).toMeasure eq01Set = 0 := by
  classical
  have hdis : Disjoint (pmf3 2).support eq01Set := by
    refine Set.disjoint_left.2 ?_
    intro w hwSupp hwEq
    have hP3 : P3 2 w = 0 := P3_two_eq_zero_of_mem_eq01Set (w := w) hwEq
    have : (pmf3 2) w = 0 := by
      simpa [pmf3] using hP3
    exact (PMF.mem_support_iff (pmf3 2) w).1 hwSupp this
  exact (PMF.toMeasure_apply_eq_zero_iff (p := pmf3 2) measurableSet_eq01Set).2 hdis

lemma measurableSet_adjEqSet (i : ℤ) : MeasurableSet (adjEqSet i) := by
  classical
  have h0 : Measurable (fun f : IcoIdx i 2 → Fin 3 => f (icoIdx0 i)) := by
    simpa using (measurable_pi_apply (a := icoIdx0 i))
  have h1 : Measurable (fun f : IcoIdx i 2 → Fin 3 => f (icoIdx1 i)) := by
    simpa using (measurable_pi_apply (a := icoIdx1 i))
  simpa [adjEqSet] using measurableSet_eq_fun h0 h1

lemma preimage_wordToIco_adjEqSet (i : ℤ) :
    (wordToIco (q := 3) i 2) ⁻¹' (adjEqSet i) = eq01Set := by
  ext w
  simp [adjEqSet, eq01Set, icoIdx0, icoIdx1, wordToIco]

lemma intervalMeasure3_adjEqSet_zero (i : ℤ) : intervalMeasure3 i 2 (adjEqSet i) = 0 := by
  classical
  have hmeas_word : Measurable (wordToIco (q := 3) i 2) := by
    simpa using (measurable_of_finite (wordToIco (q := 3) i 2))
  have hmap :
      intervalMeasure3 i 2 (adjEqSet i) = (pmf3 2).toMeasure eq01Set := by
    simp [intervalMeasure3, Measure.map_apply hmeas_word (measurableSet_adjEqSet i),
      preimage_wordToIco_adjEqSet (i := i)]
  simpa [hmap] using pmf3_two_toMeasure_eq01Set

lemma cylinder_adjEqSet (i : ℤ) :
    (cylinder (IcoIdx i 2) (adjEqSet i) : Set (ℤ → Fin 3)) = {x | x i = x (i + 1)} := by
  ext x
  simp [cylinder, adjEqSet, icoIdx0, icoIdx1, equivIco, IcoIdx]

end Three

/-! ### Identifying `P3Family` on genuine intervals -/

lemma P3Family_IcoIdx_succ (a : ℤ) (n : ℕ) :
    P3Family (IcoIdx a (n + 1)) = intervalMeasure3 a (n + 1) := by
  classical
  have hI : (IcoIdx a (n + 1)).Nonempty := by
    refine ⟨a, ?_⟩
    simp [IcoIdx]

  have hmin : (IcoIdx a (n + 1)).min' hI = a := by
    refine (Finset.min'_eq_iff (s := IcoIdx a (n + 1)) (H := hI) a).2 ?_
    constructor
    · simp [IcoIdx]
    · intro j hj
      exact (Finset.mem_Ico).1 hj |>.1

  have hmax : (IcoIdx a (n + 1)).max' hI = a + n := by
    refine (Finset.max'_eq_iff (s := IcoIdx a (n + 1)) (H := hI) (a + n)).2 ?_
    constructor
    · have hnlt : (n : ℤ) < (n + 1 : ℤ) := by
        exact_mod_cast (Nat.lt_succ_self n)
      have : (a + n : ℤ) < a + (n + 1 : ℤ) := by
        exact add_lt_add_right hnlt a
      exact (Finset.mem_Ico).2 ⟨by linarith, this⟩
    · intro j hj
      have hjlt : (j : ℤ) < a + (n + 1 : ℤ) := (Finset.mem_Ico).1 hj |>.2
      have : (j : ℤ) < (a + n) + 1 := by
        simpa [add_assoc, add_left_comm, add_comm] using hjlt
      exact (Int.lt_add_one_iff).1 this

  generalize haS : (IcoIdx a (n + 1)).min' hI = aS
  generalize hnS : ((IcoIdx a (n + 1)).max' hI + 1 - aS).toNat = nS
  have hsubS : IcoIdx a (n + 1) ⊆ IcoIdx aS nS := by
    simpa [haS, hnS] using (P3Family_hsub (I := IcoIdx a (n + 1)) hI)
  have hP :
      P3Family (IcoIdx a (n + 1)) =
        (intervalMeasure3 aS nS).map (Finset.restrict₂ (π := fun _ : ℤ => Fin 3) hsubS) := by
    cases haS
    cases hnS
    have hre :
        Finset.restrict₂ (π := fun _ : ℤ => Fin 3) (P3Family_hsub (I := IcoIdx a (n + 1)) hI) =
          Finset.restrict₂ (π := fun _ : ℤ => Fin 3) hsubS := by
      exact restrict₂_eq_of_eq (π := fun _ : ℤ => Fin 3) _ _
    simp [P3Family, hI, hre]

  have haS' : aS = a := by
    calc
      aS = (IcoIdx a (n + 1)).min' hI := by simpa using haS.symm
      _ = a := hmin
  cases haS'.symm

  have hnS' : nS = n + 1 := by
    calc
      nS = ((IcoIdx a (n + 1)).max' hI + 1 - a).toNat := by simpa using hnS.symm
      _ = (a + n + 1 - a).toNat := by simp [hmax]
      _ = (n + 1 : ℕ) := by
            have : (a + n + 1 - a : ℤ) = (n + 1 : ℤ) := by abel
            simp [this]
  cases hnS'.symm

  have hre_id :
      (Finset.restrict₂ (π := fun _ : ℤ => Fin 3) hsubS) =
        (id : (IcoIdx a (n + 1) → Fin 3) → _) := by
    have href : IcoIdx a (n + 1) ⊆ IcoIdx a (n + 1) := by
      intro x hx
      exact hx
    have hre :
        Finset.restrict₂ (π := fun _ : ℤ => Fin 3) hsubS =
          Finset.restrict₂ (π := fun _ : ℤ => Fin 3) href := by
      exact restrict₂_eq_of_eq (π := fun _ : ℤ => Fin 3) _ _
    have hid :
        Finset.restrict₂ (π := fun _ : ℤ => Fin 3) href =
          (id : (IcoIdx a (n + 1) → Fin 3) → _) := by
      funext f
      ext j
      rfl
    calc
      Finset.restrict₂ (π := fun _ : ℤ => Fin 3) hsubS =
          Finset.restrict₂ (π := fun _ : ℤ => Fin 3) href := hre
      _ = (id : (IcoIdx a (n + 1) → Fin 3) → _) := hid

  calc
    P3Family (IcoIdx a (n + 1))
        = (intervalMeasure3 a (n + 1)).map (Finset.restrict₂ (π := fun _ : ℤ => Fin 3) hsubS) := by
            simp [hP]
    _ = intervalMeasure3 a (n + 1) := by
          simp [hre_id]

lemma P3Family_IcoIdx_two (i : ℤ) : P3Family (IcoIdx i 2) = intervalMeasure3 i 2 := by
  simpa using (P3Family_IcoIdx_succ (a := i) (n := 1))

lemma μ3Measure_adjacent_eq_zero (i : ℤ) :
    μ3Measure ({x : ℤ → Fin 3 | x i = x (i + 1)} : Set (ℤ → Fin 3)) = 0 := by
  have hS : MeasurableSet (Three.adjEqSet i) := Three.measurableSet_adjEqSet i
  have hcyl :
      ({x : ℤ → Fin 3 | x i = x (i + 1)} : Set (ℤ → Fin 3))
        = cylinder (IcoIdx i 2) (Three.adjEqSet i) := by
    simpa using (Three.cylinder_adjEqSet (i := i)).symm
  rw [hcyl, μ3Measure_cylinder (I := IcoIdx i 2) (S := Three.adjEqSet i) hS]
  rw [P3Family_IcoIdx_two (i := i)]
  exact Three.intervalMeasure3_adjEqSet_zero i

theorem μ3_isColoring_ae : (μ3 : Measure (ℤ → Fin 3)) {x | IsColoring x} = 1 := by
  classical
  let E : ℤ → Set (ℤ → Fin 3) := fun i => {x | x i = x (i + 1)}
  have hE : ∀ i, (μ3 : Measure (ℤ → Fin 3)) (E i) = 0 := by
    intro i
    simpa [μ3, E] using (μ3Measure_adjacent_eq_zero (i := i))
  have hUnion : (μ3 : Measure (ℤ → Fin 3)) (⋃ i : ℤ, E i) = 0 := by
    simpa using (measure_iUnion_null hE)

  have hcompl :
      ({x : ℤ → Fin 3 | IsColoring x} : Set (ℤ → Fin 3))ᶜ = ⋃ i : ℤ, E i := by
    ext x
    simp [IsColoring, E]

  have hmeasE : ∀ i, MeasurableSet (E i) := by
    intro i
    have h0 : Measurable (fun x : ℤ → Fin 3 => x i) := measurable_pi_apply (a := i)
    have h1 : Measurable (fun x : ℤ → Fin 3 => x (i + 1)) := measurable_pi_apply (a := i + 1)
    simpa [E] using measurableSet_eq_fun h0 h1
  have hmeasColoring : MeasurableSet ({x : ℤ → Fin 3 | IsColoring x} : Set (ℤ → Fin 3)) := by
    have hmeasColoring_compl :
        MeasurableSet (({x : ℤ → Fin 3 | IsColoring x} : Set (ℤ → Fin 3))ᶜ) := by
      rw [hcompl]
      exact MeasurableSet.iUnion hmeasE
    simpa using hmeasColoring_compl.compl

  have hColoring_compl :
      (μ3 : Measure (ℤ → Fin 3)) ({x : ℤ → Fin 3 | IsColoring x} : Set (ℤ → Fin 3))ᶜ = 0 := by
    simpa [hcompl] using hUnion

  have hprob :
      (μ3 : Measure (ℤ → Fin 3)) ({x : ℤ → Fin 3 | IsColoring x} : Set (ℤ → Fin 3)) +
          (μ3 : Measure (ℤ → Fin 3)) ({x : ℤ → Fin 3 | IsColoring x} : Set (ℤ → Fin 3))ᶜ
        = 1 := by
    simpa using (MeasureTheory.prob_add_prob_compl (μ := (μ3 : Measure (ℤ → Fin 3))) hmeasColoring)
  simpa [hColoring_compl] using hprob

end Word

end FiniteDependence.Coloring
