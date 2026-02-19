import FiniteDependence.Coloring.ProcessFour
import Mathlib.MeasureTheory.Measure.Typeclasses.Finite

/-!
# Properties of the `q = 4` two-sided process

This file proves that the probability measure `Word.μ4` constructed from the projective family
`Word.P4Family` is stationary (shift-invariant).

Further properties (proper coloring almost surely, 1-dependence) will also live here.
-/

open scoped ENNReal BigOperators

namespace FiniteDependence.Coloring

namespace Word

open MeasureTheory Set

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
    (shiftFinset I → Fin 4) → (I → Fin 4) :=
  fun f i => f (shiftElem I i)

lemma shiftFinset_nonempty {I : Finset ℤ} (hI : I.Nonempty) : (shiftFinset I).Nonempty :=
  hI.image (fun z : ℤ => z + 1)

lemma measurable_precompShiftFinset (I : Finset ℤ) : Measurable (precompShiftFinset I) := by
  classical
  simpa using measurable_of_finite (precompShiftFinset I)

lemma measurable_shift : Measurable (FiniteDependence.Coloring.shift (q := 4)) := by
  simpa [FiniteDependence.Coloring.shift] using (FiniteDependence.measurable_shift (α := Fin 4))

/-! ## Cylinders and shift -/

lemma restrict_shift_eq_precomp (I : Finset ℤ) (x : ℤ → Fin 4) :
    I.restrict (FiniteDependence.Coloring.shift (q := 4) x)
      = precompShiftFinset I ((shiftFinset I).restrict x) := by
  funext i
  rfl

lemma preimage_shift_cylinder (I : Finset ℤ) (S : Set (I → Fin 4)) :
    (FiniteDependence.Coloring.shift (q := 4)) ⁻¹' (cylinder I S)
      = cylinder (shiftFinset I) ((precompShiftFinset I) ⁻¹' S) := by
  ext x
  simp [cylinder, restrict_shift_eq_precomp]

/-! ## Shift invariance of `P4Family` -/

private lemma monotone_add_one : Monotone (fun z : ℤ => z + 1) := by
  intro a b hab
  -- `a ≤ b → a+1 ≤ b+1`
  exact add_le_add_left hab 1

lemma min'_shiftFinset {I : Finset ℤ} (hI : I.Nonempty) :
    (shiftFinset I).min' (shiftFinset_nonempty (I := I) hI) = I.min' hI + 1 := by
  -- `Monotone.map_finset_min'` gives `f (min') = min' (image)`.
  simpa [shiftFinset, shiftFinset_nonempty] using
    (Monotone.map_finset_min' (α := ℤ) (β := ℤ) monotone_add_one (s := I) hI).symm

lemma max'_shiftFinset {I : Finset ℤ} (hI : I.Nonempty) :
    (shiftFinset I).max' (shiftFinset_nonempty (I := I) hI) = I.max' hI + 1 := by
  simpa [shiftFinset, shiftFinset_nonempty] using
    (Monotone.map_finset_max' (α := ℤ) (β := ℤ) monotone_add_one (s := I) hI).symm

/-- `P4Family` is equivariant under shifting indices by `+1`. -/
lemma P4Family_map_precompShiftFinset (I : Finset ℤ) :
    (P4Family (shiftFinset I)).map (precompShiftFinset I) = P4Family I := by
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
      simpa [haS, hnS] using (P4Family_hsub (I := shiftFinset I) hI')

    have hmeas_pre : Measurable (precompShiftFinset I) := measurable_precompShiftFinset I

    have hPshift :
        P4Family (shiftFinset I) =
          (intervalMeasure4 aS nS).map (Finset.restrict₂ (π := fun _ : ℤ => Fin 4) hsubS) := by
      -- `P4Family` is defined using the convex-hull interval parameters of its index finset.
      -- Here we use the generalized names `aS` and `nS`, and then eliminate them to reduce to the
      -- definitional expression.
      cases haS
      cases hnS
      have hre :
          (Finset.restrict₂ (π := fun _ : ℤ => Fin 4) (P4Family_hsub (I := shiftFinset I) hI'))
            = Finset.restrict₂ (π := fun _ : ℤ => Fin 4) hsubS := by
        exact restrict₂_eq_of_eq (π := fun _ : ℤ => Fin 4) _ _
      simp [P4Family, hI', hre]

    -- Convert the shift-hull parameters `(aS, nS)` to `(a+1, n)`.
    have haS' : aS = a + 1 := by
      calc
        aS = (shiftFinset I).min' hI' := by simpa using haS.symm
        _ = I.min' hI + 1 := by
              simpa [shiftFinset_nonempty] using (min'_shiftFinset (I := I) hI)
        _ = a + 1 := by simp [a]
    subst haS'

    have hnS' : nS = n := by
      -- `nS` is the length of the hull interval of `shiftFinset I`.
      have hmaxS : (shiftFinset I).max' hI' = I.max' hI + 1 := by
        simpa [shiftFinset_nonempty] using (max'_shiftFinset (I := I) hI)
      have hadd :
          (I.max' hI + 1 + 1 - (I.min' hI + 1) : ℤ) = I.max' hI + 1 - I.min' hI := by
        abel
      -- Expand `n` and rewrite `nS` using `hnS`.
      subst n
      -- `a = I.min' hI`.
      have : nS = ((shiftFinset I).max' hI' + 1 - (a + 1)).toNat := by
        simpa using hnS.symm
      -- Rewrite `max'` and simplify the subtraction.
      simp [this, hmaxS, a, hadd]

    subst hnS'

    have hmeas_preico : Measurable (precompShiftIcoIdx a n) := by
      simpa [a, n] using measurable_of_finite (precompShiftIcoIdx a n)
    have hmeas_res_I :
        Measurable (Finset.restrict₂ (π := fun _ : ℤ => Fin 4) (P4Family_hsub (I := I) hI)) := by
      simpa using
        (Finset.measurable_restrict₂ (X := fun _ : ℤ => Fin 4) (P4Family_hsub (I := I) hI))
    have hmeas_res_shift :
        Measurable (Finset.restrict₂ (π := fun _ : ℤ => Fin 4) hsubS) := by
      simpa using (Finset.measurable_restrict₂ (X := fun _ : ℤ => Fin 4) hsubS)

    have hcomp :
        (precompShiftFinset I) ∘ (Finset.restrict₂ (π := fun _ : ℤ => Fin 4) hsubS)
          = (Finset.restrict₂ (π := fun _ : ℤ => Fin 4) (P4Family_hsub (I := I) hI)) ∘
              precompShiftIcoIdx a n := by
      funext f
      funext i
      rfl

    -- Main calculation: reduce to `intervalMeasure4_map_precompShiftIcoIdx`.
    calc
      (P4Family (shiftFinset I)).map (precompShiftFinset I)
          = ((intervalMeasure4 (a + 1) n).map
              (Finset.restrict₂ (π := fun _ : ℤ => Fin 4) hsubS)).map (precompShiftFinset I) := by
              simp [hPshift]
      _ = (intervalMeasure4 (a + 1) n).map
            ((precompShiftFinset I) ∘ (Finset.restrict₂ (π := fun _ : ℤ => Fin 4) hsubS)) := by
              simp [Measure.map_map hmeas_pre hmeas_res_shift]
      _ = (intervalMeasure4 (a + 1) n).map
            ((Finset.restrict₂ (π := fun _ : ℤ => Fin 4) (P4Family_hsub (I := I) hI)) ∘
              precompShiftIcoIdx a n) := by
              simp [hcomp]
      _ = ((intervalMeasure4 (a + 1) n).map (precompShiftIcoIdx a n)).map
            (Finset.restrict₂ (π := fun _ : ℤ => Fin 4) (P4Family_hsub (I := I) hI)) := by
              simp [Measure.map_map hmeas_res_I hmeas_preico]
      _ = (intervalMeasure4 a n).map
            (Finset.restrict₂ (π := fun _ : ℤ => Fin 4) (P4Family_hsub (I := I) hI)) := by
              simp [intervalMeasure4_map_precompShiftIcoIdx]
      _ = P4Family I := by
              simp [P4Family, hI, a, n]
  ·
    have hI' : I = ∅ := Finset.not_nonempty_iff_eq_empty.1 hI
    subst hI'
    have hmeas : Measurable (precompShiftFinset (∅ : Finset ℤ)) :=
      measurable_precompShiftFinset (∅ : Finset ℤ)
    have hfun :
        precompShiftFinset (∅ : Finset ℤ) (fun _ : shiftFinset (∅ : Finset ℤ) => (0 : Fin 4))
          = (fun _ : (∅ : Finset ℤ) => (0 : Fin 4)) := by
      funext i
      cases i with
      | mk x hx =>
        simp at hx
    -- Avoid rewriting `shiftFinset ∅` too early: we want `hfun` to match the point of the `dirac`.
    have hmap :
        (P4Family (shiftFinset (∅ : Finset ℤ))).map (precompShiftFinset (∅ : Finset ℤ))
          =
          Measure.dirac
            (precompShiftFinset (∅ : Finset ℤ)
              (fun _ : shiftFinset (∅ : Finset ℤ) => (0 : Fin 4))) := by
      -- `shiftFinset ∅` is empty, so `P4Family` is a Dirac measure.
      have hempty : ¬(shiftFinset (∅ : Finset ℤ)).Nonempty := by
        simp [shiftFinset]
      simp [P4Family, hempty, Measure.map_dirac hmeas]
    -- Rewrite the point of the `dirac` using `hfun`.
    simpa [P4Family, shiftFinset, hfun] using hmap

/-! ## Stationarity of `μ4` -/

theorem μ4_isStationary : IsStationary (q := 4) μ4 := by
  -- We prove equality of measures by checking it on the generating π-system of measurable cylinders.
  classical
  -- Unfold the definition of stationarity.
  change (μ4Measure.map (FiniteDependence.Coloring.shift (q := 4))) = μ4Measure
  -- `ext_of_generate_finite` requires the pushforward measure to be finite.
  letI : MeasureTheory.IsFiniteMeasure (μ4Measure.map (FiniteDependence.Coloring.shift (q := 4))) :=
    MeasureTheory.IsFiniteMeasure.mk (by
      -- `(μ4Measure.map shift) univ = μ4Measure univ = 1`.
      have hμ_univ : μ4Measure univ = (1 : ℝ≥0∞) := by
        -- `μ4` is a probability measure with underlying measure `μ4Measure`.
        simpa [μ4] using
          (MeasureTheory.IsProbabilityMeasure.measure_univ (μ := (μ4 : Measure (ℤ → Fin 4))))
      have hmap_univ :
          μ4Measure.map (FiniteDependence.Coloring.shift (q := 4)) univ = (1 : ℝ≥0∞) := by
        simp [Measure.map_apply measurable_shift MeasurableSet.univ, hμ_univ]
      simp [hmap_univ])

  refine MeasureTheory.ext_of_generate_finite (μ := μ4Measure.map (FiniteDependence.Coloring.shift (q := 4)))
    (ν := μ4Measure) (C := measurableCylinders (fun _ : ℤ => Fin 4)) ?_ ?_ ?_ ?_
  · -- `MeasurableSpace.pi` is generated by measurable cylinders.
    simpa using μ4Measure_generateFrom
  · -- measurable cylinders form a π-system
    simpa using (MeasureTheory.isPiSystem_measurableCylinders (α := fun _ : ℤ => Fin 4))
  · -- equality on generators
    intro s hs
    rcases (mem_measurableCylinders _).1 hs with ⟨I, S, hS, rfl⟩
    have hmeas_cyl : MeasurableSet (cylinder I S : Set (ℤ → Fin 4)) := by
      -- `cylinder I S = I.restrict ⁻¹' S`
      have hmeas_restrict : Measurable (I.restrict : (ℤ → Fin 4) → I → Fin 4) :=
        measurable_pi_lambda _ (fun _ => measurable_pi_apply _)
      simpa [cylinder] using hS.preimage hmeas_restrict
    -- Evaluate the pushforward on cylinders.
    have :
        μ4Measure.map (FiniteDependence.Coloring.shift (q := 4)) (cylinder I S : Set (ℤ → Fin 4))
          = μ4Measure (cylinder I S : Set (ℤ → Fin 4)) := by
      -- `map` applies as a preimage under the shift.
      have hmap :
          μ4Measure.map (FiniteDependence.Coloring.shift (q := 4)) (cylinder I S : Set (ℤ → Fin 4))
            = μ4Measure ((FiniteDependence.Coloring.shift (q := 4)) ⁻¹' (cylinder I S)) := by
        simp [Measure.map_apply measurable_shift hmeas_cyl]
      -- Rewrite the preimage cylinder and use the cylinder formula.
      rw [hmap, preimage_shift_cylinder (I := I) (S := S)]
      have hS' : MeasurableSet ((precompShiftFinset I) ⁻¹' S) :=
        (measurable_precompShiftFinset I) hS
      have hmeas_precomp : Measurable (precompShiftFinset I) := measurable_precompShiftFinset I
      calc
        μ4Measure (cylinder (shiftFinset I) ((precompShiftFinset I) ⁻¹' S) : Set (ℤ → Fin 4))
            = P4Family (shiftFinset I) ((precompShiftFinset I) ⁻¹' S) := by
                exact μ4Measure_cylinder (I := shiftFinset I)
                  (S := (precompShiftFinset I ⁻¹' S)) hS'
        _ = ((P4Family (shiftFinset I)).map (precompShiftFinset I)) S := by
              simp [Measure.map_apply hmeas_precomp hS]
        _ = P4Family I S := by
              -- Apply the shift-equivariance lemma.
              simpa using congrArg (fun μ => μ S) (P4Family_map_precompShiftFinset (I := I))
        _ = μ4Measure (cylinder I S : Set (ℤ → Fin 4)) := by
              exact (μ4Measure_cylinder (I := I) (S := S) hS).symm
    simpa using this
  · -- equality on `univ`
    simp [Measure.map_apply measurable_shift MeasurableSet.univ]

/-! ## Almost-sure properness -/

/-- The index `i` inside `IcoIdx i 2` corresponding to `0 : Fin 2`. -/
noncomputable def icoIdx0 (i : ℤ) : IcoIdx i 2 :=
  (equivIco i 2) (0 : Fin 2)

/-- The index `i+1` inside `IcoIdx i 2` corresponding to `1 : Fin 2`. -/
noncomputable def icoIdx1 (i : ℤ) : IcoIdx i 2 :=
  (equivIco i 2) (1 : Fin 2)

/-- Words of length `2` with equal adjacent letters. -/
def eq01Set : Set (Word 4 2) :=
  {w | w (0 : Fin 2) = w (1 : Fin 2)}

/-- Interval assignments on `[i, i+2)` with equal adjacent values. -/
def adjEqSet (i : ℤ) : Set (IcoIdx i 2 → Fin 4) :=
  {f | f (icoIdx0 i) = f (icoIdx1 i)}

lemma measurableSet_eq01Set : MeasurableSet (eq01Set) := by
  classical
  have h0 : Measurable (fun w : Word 4 2 => w (0 : Fin 2)) := by
    simpa using (measurable_pi_apply (a := (0 : Fin 2)))
  have h1 : Measurable (fun w : Word 4 2 => w (1 : Fin 2)) := by
    simpa using (measurable_pi_apply (a := (1 : Fin 2)))
  simpa [eq01Set] using measurableSet_eq_fun h0 h1

lemma P4_two_eq_zero_of_mem_eq01Set {w : Word 4 2} (hw : w ∈ eq01Set) : P4 2 w = 0 := by
  have h : w (0 : Fin 2) = w (1 : Fin 2) := hw
  have hnot : ¬ IsProper w := by
    simpa [IsProper] using h
  have hB : B (q := 4) w = 0 := by
    simpa using (B_eq_zero_of_not_isProper (q := 4) (x := w) (n := 1) hnot)
  simp [P4, hB]

lemma pmf4_two_toMeasure_eq01Set : (pmf4 2).toMeasure eq01Set = 0 := by
  classical
  have hdis : Disjoint (pmf4 2).support eq01Set := by
    refine Set.disjoint_left.2 ?_
    intro w hwSupp hwEq
    have hP4 : P4 2 w = 0 := P4_two_eq_zero_of_mem_eq01Set (w := w) hwEq
    have : (pmf4 2) w = 0 := by
      simpa [pmf4] using hP4
    exact (PMF.mem_support_iff (pmf4 2) w).1 hwSupp this
  exact (PMF.toMeasure_apply_eq_zero_iff (p := pmf4 2) measurableSet_eq01Set).2 hdis

lemma measurableSet_adjEqSet (i : ℤ) : MeasurableSet (adjEqSet i) := by
  classical
  have h0 : Measurable (fun f : IcoIdx i 2 → Fin 4 => f (icoIdx0 i)) := by
    simpa using (measurable_pi_apply (a := icoIdx0 i))
  have h1 : Measurable (fun f : IcoIdx i 2 → Fin 4 => f (icoIdx1 i)) := by
    simpa using (measurable_pi_apply (a := icoIdx1 i))
  simpa [adjEqSet] using measurableSet_eq_fun h0 h1

lemma preimage_wordToIco_adjEqSet (i : ℤ) :
    (wordToIco (q := 4) i 2) ⁻¹' (adjEqSet i) = eq01Set := by
  ext w
  simp [adjEqSet, eq01Set, icoIdx0, icoIdx1, wordToIco]

lemma intervalMeasure4_adjEqSet_zero (i : ℤ) : intervalMeasure4 i 2 (adjEqSet i) = 0 := by
  classical
  have hmeas_word : Measurable (wordToIco (q := 4) i 2) := by
    simpa using (measurable_of_finite (wordToIco (q := 4) i 2))
  have hmap :
      intervalMeasure4 i 2 (adjEqSet i) = (pmf4 2).toMeasure eq01Set := by
    simp [intervalMeasure4, Measure.map_apply hmeas_word (measurableSet_adjEqSet i),
      preimage_wordToIco_adjEqSet (i := i)]
  simpa [hmap] using pmf4_two_toMeasure_eq01Set

lemma cylinder_adjEqSet (i : ℤ) :
    (cylinder (IcoIdx i 2) (adjEqSet i) : Set (ℤ → Fin 4)) = {x | x i = x (i + 1)} := by
  ext x
  simp [cylinder, adjEqSet, icoIdx0, icoIdx1, equivIco, IcoIdx]

/-! ### Identifying `P4Family` on genuine intervals -/

lemma P4Family_IcoIdx_succ (a : ℤ) (n : ℕ) :
    P4Family (IcoIdx a (n + 1)) = intervalMeasure4 a (n + 1) := by
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
    · -- `a+n ∈ [a, a+(n+1))`.
      have hnlt : (n : ℤ) < (n + 1 : ℤ) := by
        exact_mod_cast (Nat.lt_succ_self n)
      have : (a + n : ℤ) < a + (n + 1 : ℤ) := by
        exact add_lt_add_right hnlt a
      exact (Finset.mem_Ico).2 ⟨by linarith, this⟩
    · intro j hj
      have hjlt : (j : ℤ) < a + (n + 1 : ℤ) := (Finset.mem_Ico).1 hj |>.2
      have : (j : ℤ) < (a + n) + 1 := by
        simpa [add_assoc, add_left_comm, add_comm] using hjlt
      exact (Int.lt_add_one_iff).1 this

  -- Generalize the hull parameters used by `P4Family` and reduce to the definitional expression.
  generalize haS : (IcoIdx a (n + 1)).min' hI = aS
  generalize hnS : ((IcoIdx a (n + 1)).max' hI + 1 - aS).toNat = nS
  have hsubS : IcoIdx a (n + 1) ⊆ IcoIdx aS nS := by
    simpa [haS, hnS] using (P4Family_hsub (I := IcoIdx a (n + 1)) hI)
  have hP :
      P4Family (IcoIdx a (n + 1)) =
        (intervalMeasure4 aS nS).map (Finset.restrict₂ (π := fun _ : ℤ => Fin 4) hsubS) := by
    cases haS
    cases hnS
    have hre :
        Finset.restrict₂ (π := fun _ : ℤ => Fin 4) (P4Family_hsub (I := IcoIdx a (n + 1)) hI) =
          Finset.restrict₂ (π := fun _ : ℤ => Fin 4) hsubS := by
      exact restrict₂_eq_of_eq (π := fun _ : ℤ => Fin 4) _ _
    simp [P4Family, hI, hre]

  -- Replace `aS` by `a`.
  have haS' : aS = a := by
    calc
      aS = (IcoIdx a (n + 1)).min' hI := by simpa using haS.symm
      _ = a := hmin
  cases haS'.symm

  -- Replace `nS` by `n+1`.
  have hnS' : nS = n + 1 := by
    calc
      nS = ((IcoIdx a (n + 1)).max' hI + 1 - a).toNat := by simpa using hnS.symm
      _ = (a + n + 1 - a).toNat := by simp [hmax]
      _ = (n + 1 : ℕ) := by
            have : (a + n + 1 - a : ℤ) = (n + 1 : ℤ) := by abel
            simp [this]
  cases hnS'.symm

  -- Now the restriction map is the identity.
  have hre_id :
      (Finset.restrict₂ (π := fun _ : ℤ => Fin 4) hsubS) =
        (id : (IcoIdx a (n + 1) → Fin 4) → _) := by
    have href : IcoIdx a (n + 1) ⊆ IcoIdx a (n + 1) := by
      intro x hx
      exact hx
    have hre :
        Finset.restrict₂ (π := fun _ : ℤ => Fin 4) hsubS =
          Finset.restrict₂ (π := fun _ : ℤ => Fin 4) href := by
      exact restrict₂_eq_of_eq (π := fun _ : ℤ => Fin 4) _ _
    have hid :
        Finset.restrict₂ (π := fun _ : ℤ => Fin 4) href =
          (id : (IcoIdx a (n + 1) → Fin 4) → _) := by
      funext f
      ext j
      rfl
    calc
      Finset.restrict₂ (π := fun _ : ℤ => Fin 4) hsubS =
          Finset.restrict₂ (π := fun _ : ℤ => Fin 4) href := hre
      _ = (id : (IcoIdx a (n + 1) → Fin 4) → _) := hid

  calc
    P4Family (IcoIdx a (n + 1))
        = (intervalMeasure4 a (n + 1)).map (Finset.restrict₂ (π := fun _ : ℤ => Fin 4) hsubS) := by
            simp [hP]
    _ = intervalMeasure4 a (n + 1) := by
          simp [hre_id]

lemma P4Family_IcoIdx_two (i : ℤ) : P4Family (IcoIdx i 2) = intervalMeasure4 i 2 := by
  simpa using (P4Family_IcoIdx_succ (a := i) (n := 1))

lemma μ4Measure_adjacent_eq_zero (i : ℤ) :
    μ4Measure ({x : ℤ → Fin 4 | x i = x (i + 1)} : Set (ℤ → Fin 4)) = 0 := by
  have hS : MeasurableSet (adjEqSet i) := measurableSet_adjEqSet i
  -- Rewrite as a cylinder, use the cylinder formula, and reduce to `intervalMeasure4`.
  have hcyl :
      ({x : ℤ → Fin 4 | x i = x (i + 1)} : Set (ℤ → Fin 4))
        = cylinder (IcoIdx i 2) (adjEqSet i) := by
    simpa using (cylinder_adjEqSet (i := i)).symm
  rw [hcyl, μ4Measure_cylinder (I := IcoIdx i 2) (S := adjEqSet i) hS]
  -- Identify `P4Family (IcoIdx i 2)` with `intervalMeasure4 i 2`.
  rw [P4Family_IcoIdx_two (i := i)]
  exact intervalMeasure4_adjEqSet_zero i

theorem μ4_isColoring_ae : (μ4 : Measure (ℤ → Fin 4)) {x | IsColoring x} = 1 := by
  classical
  let E : ℤ → Set (ℤ → Fin 4) := fun i => {x | x i = x (i + 1)}
  have hE : ∀ i, (μ4 : Measure (ℤ → Fin 4)) (E i) = 0 := by
    intro i
    -- `μ4` has underlying measure `μ4Measure`.
    simpa [μ4, E] using (μ4Measure_adjacent_eq_zero (i := i))
  have hUnion : (μ4 : Measure (ℤ → Fin 4)) (⋃ i : ℤ, E i) = 0 := by
    simpa using (measure_iUnion_null hE)

  have hcompl :
      ({x : ℤ → Fin 4 | IsColoring x} : Set (ℤ → Fin 4))ᶜ = ⋃ i : ℤ, E i := by
    ext x
    simp [IsColoring, E]

  have hmeasE : ∀ i, MeasurableSet (E i) := by
    intro i
    have h0 : Measurable (fun x : ℤ → Fin 4 => x i) := measurable_pi_apply (a := i)
    have h1 : Measurable (fun x : ℤ → Fin 4 => x (i + 1)) := measurable_pi_apply (a := i + 1)
    simpa [E] using measurableSet_eq_fun h0 h1
  have hmeasColoring : MeasurableSet ({x : ℤ → Fin 4 | IsColoring x} : Set (ℤ → Fin 4)) := by
    have hmeasColoring_compl :
        MeasurableSet (({x : ℤ → Fin 4 | IsColoring x} : Set (ℤ → Fin 4))ᶜ) := by
      -- `IsColoring` fails iff there exists an index with equal adjacent colors.
      rw [hcompl]
      exact MeasurableSet.iUnion hmeasE
    simpa using hmeasColoring_compl.compl

  have hColoring_compl : (μ4 : Measure (ℤ → Fin 4)) ({x : ℤ → Fin 4 | IsColoring x} : Set (ℤ → Fin 4))ᶜ = 0 := by
    simpa [hcompl] using hUnion

  -- For a probability measure, `μ s + μ sᶜ = 1`.
  have hprob :
      (μ4 : Measure (ℤ → Fin 4)) ({x : ℤ → Fin 4 | IsColoring x} : Set (ℤ → Fin 4)) +
          (μ4 : Measure (ℤ → Fin 4)) ({x : ℤ → Fin 4 | IsColoring x} : Set (ℤ → Fin 4))ᶜ
        = 1 := by
    simpa using (MeasureTheory.prob_add_prob_compl (μ := (μ4 : Measure (ℤ → Fin 4))) hmeasColoring)
  simpa [hColoring_compl] using hprob

end Word

end FiniteDependence.Coloring
