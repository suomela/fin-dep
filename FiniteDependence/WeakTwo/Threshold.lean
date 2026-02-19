import FiniteDependence.API.Definitions
import FiniteDependence.Core.MeasurablePredicates
import FiniteDependence.Coloring.Existence
import FiniteDependence.Coloring.MeasureHelpers
import FiniteDependence.MIS.LowerBounds.K5.Bridge

import Mathlib.MeasureTheory.Measure.Map
import Mathlib.MeasureTheory.MeasurableSpace.Prod
import Mathlib.Tactic

/-!
# Weak 2-coloring threshold on `ℤ`

We formalize the threshold for binary weak 2-colorings (forbidden patterns `000` and `111`):

* existence of a stationary `3`-dependent law;
* non-existence of a stationary `2`-dependent law.

The lower bound uses an explicit local factor to MIS and the already-proved theorem
`LowerBoundBridge.not_exists_stationary_fiveDependent_MIS`.
-/

namespace FiniteDependence

open MeasureTheory ProbabilityTheory Set

namespace WeakTwo

/-! ## Shared measurability/independence helpers -/

private lemma measurable_shift (q : ℕ) : Measurable (FiniteDependence.Coloring.shift (q := q)) :=
  FiniteDependence.Coloring.measurable_shift q

private lemma measurable_apply_past {q : ℕ} (i j : ℤ) (hj : j < i) :
    Measurable[FiniteDependence.Coloring.pastMeasurableSpace (q := q) i] fun x : ℤ → Fin q => x j :=
  FiniteDependence.Coloring.measurable_apply_past (q := q) (i := i) (j := j) hj

private lemma measurable_apply_future {q : ℕ} (i : ℤ) (k : ℕ) (j : ℤ) (hj : i + k ≤ j) :
    Measurable[FiniteDependence.Coloring.futureMeasurableSpace (q := q) i k] fun x : ℤ → Fin q => x j :=
  FiniteDependence.Coloring.measurable_apply_future (q := q) (i := i) (k := k) (j := j) hj

private lemma pastMeasurableSpace_le (q : ℕ) (i : ℤ) :
    FiniteDependence.Coloring.pastMeasurableSpace (q := q) i
      ≤ (MeasurableSpace.pi : MeasurableSpace (ℤ → Fin q)) :=
  FiniteDependence.Coloring.pastMeasurableSpace_le q i

private lemma futureMeasurableSpace_le (q : ℕ) (i : ℤ) (k : ℕ) :
    FiniteDependence.Coloring.futureMeasurableSpace (q := q) i k
      ≤ (MeasurableSpace.pi : MeasurableSpace (ℤ → Fin q)) :=
  FiniteDependence.Coloring.futureMeasurableSpace_le q i k

private lemma indep_map_of_indep_comap {Ω Ω' : Type*} [MeasurableSpace Ω]
    (mΩ' : MeasurableSpace Ω') {μ : Measure Ω} {f : Ω → Ω'} (hf : AEMeasurable f μ)
    {m₁ m₂ : MeasurableSpace Ω'} (hm₁ : m₁ ≤ mΩ') (hm₂ : m₂ ≤ mΩ')
    (h : Indep (m₁.comap f) (m₂.comap f) μ) :
    Indep m₁ m₂ (@Measure.map Ω Ω' _ mΩ' f μ) :=
  FiniteDependence.Coloring.indep_map_of_indep_comap
    (mΩ' := mΩ') (μ := μ) (f := f) (hf := hf) (hm₁ := hm₁) (hm₂ := hm₂) h

/-! ## Existence: stationary 3-dependent weak-2-coloring -/

private def ascentPair (p : Fin 3 × Fin 3) : Fin 2 :=
  if p.1 < p.2 then 1 else 0

private def weakTwoFromThree (c : ℤ → Fin 3) : ℤ → Fin 2 :=
  fun i => ascentPair (c i, c (i + 1))

private lemma measurable_ascentPair : Measurable ascentPair := by
  classical
  simpa [ascentPair] using
    (Measurable.of_discrete : Measurable (fun p : Fin 3 × Fin 3 => if p.1 < p.2 then (1 : Fin 2) else 0))

private lemma measurable_weakTwoFromThree_at {m : MeasurableSpace (ℤ → Fin 3)} (i : ℤ)
    (h0 : Measurable[m] fun c : ℤ → Fin 3 => c i)
    (h1 : Measurable[m] fun c : ℤ → Fin 3 => c (i + 1)) :
    Measurable[m] fun c : ℤ → Fin 3 => weakTwoFromThree c i := by
  have hpair : Measurable[m] fun c : ℤ → Fin 3 => (c i, c (i + 1)) := h0.prodMk h1
  simpa [weakTwoFromThree] using measurable_ascentPair.comp hpair

private lemma measurable_weakTwoFromThree : Measurable weakTwoFromThree := by
  classical
  refine measurable_pi_lambda _ (fun i => ?_)
  exact measurable_weakTwoFromThree_at (m := inferInstance) (i := i)
    (h0 := by simpa using (measurable_pi_apply (a := i)))
    (h1 := by simpa using (measurable_pi_apply (a := i + 1)))

private lemma weakTwoFromThree_shift (c : ℤ → Fin 3) :
    weakTwoFromThree (FiniteDependence.Coloring.shift (q := 3) c)
      = FiniteDependence.Coloring.shift (q := 2) (weakTwoFromThree c) := by
  ext i
  simp [weakTwoFromThree, ascentPair, FiniteDependence.Coloring.shift, FiniteDependence.shift,
    add_assoc, add_left_comm, add_comm]

private lemma ascent_no111_local :
    ∀ a b c d : Fin 3,
      ¬(ascentPair (a, b) = 1 ∧ ascentPair (b, c) = 1 ∧ ascentPair (c, d) = 1) := by
  decide

private lemma ascent_no000_local :
    ∀ a b c d : Fin 3, a ≠ b → b ≠ c → c ≠ d →
      ¬(ascentPair (a, b) = 0 ∧ ascentPair (b, c) = 0 ∧ ascentPair (c, d) = 0) := by
  decide

private lemma weakTwoFromThree_isWeak_of_isColoring (c : ℤ → Fin 3) (hc : FiniteDependence.Coloring.IsColoring (q := 3) c) :
    IsWeakTwoColoring (weakTwoFromThree c) := by
  refine ⟨?_, ?_⟩
  · intro i hi
    rcases hi with ⟨h0, h1, h2⟩
    have hne01 : c i ≠ c (i + 1) := hc i
    have hne12 : c (i + 1) ≠ c (i + 2) := by simpa [add_assoc] using hc (i + 1)
    have hne23 : c (i + 2) ≠ c (i + 3) := by simpa [add_assoc] using hc (i + 2)
    have hloc := ascent_no000_local (a := c i) (b := c (i + 1)) (c := c (i + 2)) (d := c (i + 3))
      hne01 hne12 hne23
    have ha0 : ascentPair (c i, c (i + 1)) = 0 := by simpa [weakTwoFromThree] using h0
    have ha1 : ascentPair (c (i + 1), c (i + 2)) = 0 := by
      simpa [weakTwoFromThree, add_assoc] using h1
    have ha2 : ascentPair (c (i + 2), c (i + 3)) = 0 := by
      simpa [weakTwoFromThree, add_assoc] using h2
    exact hloc ⟨ha0, ha1, ha2⟩
  · intro i hi
    rcases hi with ⟨h0, h1, h2⟩
    have hloc := ascent_no111_local (a := c i) (b := c (i + 1)) (c := c (i + 2)) (d := c (i + 3))
    have ha0 : ascentPair (c i, c (i + 1)) = 1 := by simpa [weakTwoFromThree] using h0
    have ha1 : ascentPair (c (i + 1), c (i + 2)) = 1 := by
      simpa [weakTwoFromThree, add_assoc] using h1
    have ha2 : ascentPair (c (i + 2), c (i + 3)) = 1 := by
      simpa [weakTwoFromThree, add_assoc] using h2
    exact hloc ⟨ha0, ha1, ha2⟩

private lemma comap_past_le_weak (i : ℤ) :
    (FiniteDependence.Coloring.pastMeasurableSpace (q := 2) i).comap weakTwoFromThree
      ≤ FiniteDependence.Coloring.pastMeasurableSpace (q := 3) (i + 1) := by
  classical
  unfold FiniteDependence.Coloring.pastMeasurableSpace FiniteDependence.pastMeasurableSpace
  simp [MeasurableSpace.comap_iSup, MeasurableSpace.comap_comp]
  intro a ha
  have h0 : a < i + 1 := by linarith [ha]
  have h1 : a + 1 < i + 1 := by linarith [ha]
  have hm0 : Measurable[FiniteDependence.Coloring.pastMeasurableSpace (q := 3) (i + 1)]
      fun c : ℤ → Fin 3 => c a :=
    measurable_apply_past (q := 3) (i := i + 1) (j := a) h0
  have hm1 : Measurable[FiniteDependence.Coloring.pastMeasurableSpace (q := 3) (i + 1)]
      fun c : ℤ → Fin 3 => c (a + 1) :=
    measurable_apply_past (q := 3) (i := i + 1) (j := a + 1) h1
  have hmeas :
      Measurable[FiniteDependence.Coloring.pastMeasurableSpace (q := 3) (i + 1)]
        fun c : ℤ → Fin 3 => weakTwoFromThree c a :=
    measurable_weakTwoFromThree_at
      (m := FiniteDependence.Coloring.pastMeasurableSpace (q := 3) (i + 1)) (i := a)
      (h0 := hm0) (h1 := hm1)
  simpa [Function.comp] using hmeas.comap_le

private lemma comap_future_le_weak (i : ℤ) :
    (FiniteDependence.Coloring.futureMeasurableSpace (q := 2) i 3).comap weakTwoFromThree
      ≤ FiniteDependence.Coloring.futureMeasurableSpace (q := 3) (i + 1) 2 := by
  classical
  unfold FiniteDependence.Coloring.futureMeasurableSpace FiniteDependence.futureMeasurableSpace
  simp [MeasurableSpace.comap_iSup, MeasurableSpace.comap_comp]
  intro a ha
  have h0 : i + 1 + 2 ≤ a := by linarith [ha]
  have h1 : i + 1 + 2 ≤ a + 1 := by linarith [ha]
  have hm0 : Measurable[FiniteDependence.Coloring.futureMeasurableSpace (q := 3) (i + 1) 2]
      fun c : ℤ → Fin 3 => c a :=
    measurable_apply_future (q := 3) (i := i + 1) (k := 2) (j := a) h0
  have hm1 : Measurable[FiniteDependence.Coloring.futureMeasurableSpace (q := 3) (i + 1) 2]
      fun c : ℤ → Fin 3 => c (a + 1) :=
    measurable_apply_future (q := 3) (i := i + 1) (k := 2) (j := a + 1) h1
  have hmeas :
      Measurable[FiniteDependence.Coloring.futureMeasurableSpace (q := 3) (i + 1) 2]
        fun c : ℤ → Fin 3 => weakTwoFromThree c a :=
    measurable_weakTwoFromThree_at
      (m := FiniteDependence.Coloring.futureMeasurableSpace (q := 3) (i + 1) 2) (i := a)
      (h0 := hm0) (h1 := hm1)
  simpa [Function.comp] using hmeas.comap_le

private lemma comap_future_le_weak_k2 (i : ℤ) :
    (FiniteDependence.Coloring.futureMeasurableSpace (q := 2) i 2).comap weakTwoFromThree
      ≤ FiniteDependence.Coloring.futureMeasurableSpace (q := 3) (i + 1) 1 := by
  classical
  unfold FiniteDependence.Coloring.futureMeasurableSpace FiniteDependence.futureMeasurableSpace
  simp [MeasurableSpace.comap_iSup, MeasurableSpace.comap_comp]
  intro a ha
  have h0 : i + 1 + 1 ≤ a := by linarith [ha]
  have h1 : i + 1 + 1 ≤ a + 1 := by linarith [ha]
  have hm0 : Measurable[FiniteDependence.Coloring.futureMeasurableSpace (q := 3) (i + 1) 1]
      fun c : ℤ → Fin 3 => c a :=
    measurable_apply_future (q := 3) (i := i + 1) (k := 1) (j := a) h0
  have hm1 : Measurable[FiniteDependence.Coloring.futureMeasurableSpace (q := 3) (i + 1) 1]
      fun c : ℤ → Fin 3 => c (a + 1) :=
    measurable_apply_future (q := 3) (i := i + 1) (k := 1) (j := a + 1) h1
  have hmeas :
      Measurable[FiniteDependence.Coloring.futureMeasurableSpace (q := 3) (i + 1) 1]
        fun c : ℤ → Fin 3 => weakTwoFromThree c a :=
    measurable_weakTwoFromThree_at
      (m := FiniteDependence.Coloring.futureMeasurableSpace (q := 3) (i + 1) 1) (i := a)
      (h0 := hm0) (h1 := hm1)
  simpa [Function.comp] using hmeas.comap_le

/-- A stationary `3`-dependent weak-2-coloring law exists on `ℤ`. -/
theorem exists_stationary_threeDependent_weakTwoColoring :
    ExistsStationaryKDependentWeakTwoColoring 3 := by
  classical
  rcases FiniteDependence.Coloring.exists_stationary_twoDependent_threeColoring with
    ⟨μ3, hstat3, hkdep3, hcol3⟩
  let μ : ProbabilityMeasure (ℤ → Fin 2) := μ3.map measurable_weakTwoFromThree.aemeasurable
  refine ⟨μ, ?_⟩
  refine ⟨?_, ?_, ?_⟩
  · -- Stationarity of the factor.
    have hcomm :
        (FiniteDependence.Coloring.shift (q := 2)) ∘ weakTwoFromThree
          = weakTwoFromThree ∘ (FiniteDependence.Coloring.shift (q := 3)) := by
      funext c
      simpa [Function.comp] using (weakTwoFromThree_shift c).symm
    have hmeas_shift2 : Measurable (FiniteDependence.Coloring.shift (q := 2)) := measurable_shift 2
    have hmeas_shift3 : Measurable (FiniteDependence.Coloring.shift (q := 3)) := measurable_shift 3
    change ((μ : Measure (ℤ → Fin 2)).map (FiniteDependence.Coloring.shift (q := 2)))
      = (μ : Measure (ℤ → Fin 2))
    have hstat3' :
        ((μ3 : Measure (ℤ → Fin 3)).map (FiniteDependence.Coloring.shift (q := 3)))
          = (μ3 : Measure (ℤ → Fin 3)) := hstat3
    calc
      ((μ : Measure (ℤ → Fin 2)).map (FiniteDependence.Coloring.shift (q := 2)))
          = (((μ3 : Measure (ℤ → Fin 3)).map weakTwoFromThree).map
              (FiniteDependence.Coloring.shift (q := 2))) := by
              rfl
      _ = (μ3 : Measure (ℤ → Fin 3)).map ((FiniteDependence.Coloring.shift (q := 2)) ∘ weakTwoFromThree) := by
            simpa using (Measure.map_map (μ := (μ3 : Measure (ℤ → Fin 3))) hmeas_shift2
              measurable_weakTwoFromThree)
      _ = (μ3 : Measure (ℤ → Fin 3)).map (weakTwoFromThree ∘ (FiniteDependence.Coloring.shift (q := 3))) := by
            simp [hcomm]
      _ = (((μ3 : Measure (ℤ → Fin 3)).map (FiniteDependence.Coloring.shift (q := 3))).map weakTwoFromThree) := by
            symm
            simpa using (Measure.map_map (μ := (μ3 : Measure (ℤ → Fin 3))) measurable_weakTwoFromThree
              hmeas_shift3)
      _ = (μ3 : Measure (ℤ → Fin 3)).map weakTwoFromThree := by
            simp [hstat3']
      _ = (μ : Measure (ℤ → Fin 2)) := rfl
  · -- 3-dependence from 2-dependence and one-sided radius 1.
    have hkdepMap : FiniteDependence.Coloring.IsKDependent (q := 2) μ 3 := by
      intro i
      have hbase :
          Indep (FiniteDependence.Coloring.pastMeasurableSpace (q := 3) (i + 1))
            (FiniteDependence.Coloring.futureMeasurableSpace (q := 3) (i + 1) 2)
            (μ := (μ3 : Measure (ℤ → Fin 3))) := hkdep3 (i + 1)
      have hcomap :
          Indep ((FiniteDependence.Coloring.pastMeasurableSpace (q := 2) i).comap weakTwoFromThree)
            ((FiniteDependence.Coloring.futureMeasurableSpace (q := 2) i 3).comap weakTwoFromThree)
              (μ := (μ3 : Measure (ℤ → Fin 3))) := by
        have h1 :
            Indep ((FiniteDependence.Coloring.pastMeasurableSpace (q := 2) i).comap weakTwoFromThree)
              (FiniteDependence.Coloring.futureMeasurableSpace (q := 3) (i + 1) 2)
                (μ := (μ3 : Measure (ℤ → Fin 3))) :=
          indep_of_indep_of_le_left hbase (comap_past_le_weak (i := i))
        exact indep_of_indep_of_le_right h1 (comap_future_le_weak (i := i))
      have hmap :
          Indep (FiniteDependence.Coloring.pastMeasurableSpace (q := 2) i)
            (FiniteDependence.Coloring.futureMeasurableSpace (q := 2) i 3)
            (μ :=
              @Measure.map (ℤ → Fin 3) (ℤ → Fin 2) MeasurableSpace.pi MeasurableSpace.pi weakTwoFromThree
                (μ3 : Measure (ℤ → Fin 3))) := by
        refine
          indep_map_of_indep_comap (mΩ' := (MeasurableSpace.pi : MeasurableSpace (ℤ → Fin 2)))
            (μ := (μ3 : Measure (ℤ → Fin 3))) (f := weakTwoFromThree)
            (hf := measurable_weakTwoFromThree.aemeasurable) (hm₁ := ?_) (hm₂ := ?_) hcomap
        · simpa using pastMeasurableSpace_le (q := 2) i
        · simpa using futureMeasurableSpace_le (q := 2) i 3
      simpa [μ, ProbabilityMeasure.map] using hmap
    simpa [IsKDependentCut, FiniteDependence.Coloring.IsKDependent] using hkdepMap
  · -- Weak-2 support from proper-coloring support.
    have hpre :
        (μ3 : Measure (ℤ → Fin 3)) (weakTwoFromThree ⁻¹' {x : ℤ → Fin 2 | IsWeakTwoColoring x}) = 1 := by
      have hsub :
          {c : ℤ → Fin 3 | FiniteDependence.Coloring.IsColoring (q := 3) c}
            ⊆ weakTwoFromThree ⁻¹' {x : ℤ → Fin 2 | IsWeakTwoColoring x} := by
        intro c hc
        exact weakTwoFromThree_isWeak_of_isColoring c hc
      have hle :
          (μ3 : Measure (ℤ → Fin 3)) {c : ℤ → Fin 3 | FiniteDependence.Coloring.IsColoring (q := 3) c}
            ≤ (μ3 : Measure (ℤ → Fin 3))
                (weakTwoFromThree ⁻¹' {x : ℤ → Fin 2 | IsWeakTwoColoring x}) :=
        measure_mono hsub
      have hle1 :
          (μ3 : Measure (ℤ → Fin 3)) (weakTwoFromThree ⁻¹' {x : ℤ → Fin 2 | IsWeakTwoColoring x}) ≤ 1 := by
        have : (μ3 : Measure (ℤ → Fin 3))
            (weakTwoFromThree ⁻¹' {x : ℤ → Fin 2 | IsWeakTwoColoring x})
              ≤ (μ3 : Measure (ℤ → Fin 3)) Set.univ := measure_mono (subset_univ _)
        simpa using this
      have hcol : (μ3 : Measure (ℤ → Fin 3))
          {c : ℤ → Fin 3 | FiniteDependence.Coloring.IsColoring (q := 3) c} = 1 := hcol3
      have hge : (1 : ENNReal) ≤
          (μ3 : Measure (ℤ → Fin 3)) (weakTwoFromThree ⁻¹' {x : ℤ → Fin 2 | IsWeakTwoColoring x}) := by
        simpa [hcol] using hle
      exact le_antisymm hle1 hge
    have hmap :
        (μ : Measure (ℤ → Fin 2)) {x : ℤ → Fin 2 | IsWeakTwoColoring x}
          = (μ3 : Measure (ℤ → Fin 3)) (weakTwoFromThree ⁻¹' {x : ℤ → Fin 2 | IsWeakTwoColoring x}) := by
      simpa [μ] using
        (ProbabilityMeasure.map_apply' μ3 measurable_weakTwoFromThree.aemeasurable
          FiniteDependence.measurableSet_isWeakTwoColoring)
    calc
      (μ : Measure (ℤ → Fin 2)) {x : ℤ → Fin 2 | IsWeakTwoColoring x}
          = (μ3 : Measure (ℤ → Fin 3)) (weakTwoFromThree ⁻¹' {x : ℤ → Fin 2 | IsWeakTwoColoring x}) := hmap
      _ = 1 := hpre

/-! ## Reduction map from weak-2-colorings to MIS -/

private def misFactor4 : Fin 2 → Fin 2 → Fin 2 → Fin 2 → Fin 2
  | 0, 0, 1, 0 => 1
  | 0, 0, 1, 1 => 1
  | 1, 0, 1, 0 => 1
  | 1, 0, 1, 1 => 1
  | 1, 1, 0, 0 => 1
  | _, _, _, _ => 0

private def misFromWeak (x : ℤ → Fin 2) : ℤ → Fin 2 :=
  fun i => misFactor4 (x i) (x (i + 1)) (x (i + 2)) (x (i + 3))

private def misFactor4Tuple (t : Fin 2 × Fin 2 × Fin 2 × Fin 2) : Fin 2 :=
  misFactor4 t.1 t.2.1 t.2.2.1 t.2.2.2

private lemma measurable_misFactor4Tuple : Measurable misFactor4Tuple := by
  classical
  simpa [misFactor4Tuple] using (Measurable.of_discrete : Measurable misFactor4Tuple)

private lemma measurable_misFromWeak_at {m : MeasurableSpace (ℤ → Fin 2)} (i : ℤ)
    (h0 : Measurable[m] fun x : ℤ → Fin 2 => x i)
    (h1 : Measurable[m] fun x : ℤ → Fin 2 => x (i + 1))
    (h2 : Measurable[m] fun x : ℤ → Fin 2 => x (i + 2))
    (h3 : Measurable[m] fun x : ℤ → Fin 2 => x (i + 3)) :
    Measurable[m] fun x : ℤ → Fin 2 => misFromWeak x i := by
  have htuple : Measurable[m] fun x : ℤ → Fin 2 => (x i, x (i + 1), x (i + 2), x (i + 3)) :=
    h0.prodMk (h1.prodMk (h2.prodMk h3))
  simpa [misFromWeak, misFactor4Tuple] using measurable_misFactor4Tuple.comp htuple

private lemma measurable_misFromWeak : Measurable misFromWeak := by
  classical
  refine measurable_pi_lambda _ (fun i => ?_)
  exact measurable_misFromWeak_at (m := inferInstance) (i := i)
    (h0 := by simpa using (measurable_pi_apply (a := i)))
    (h1 := by simpa using (measurable_pi_apply (a := i + 1)))
    (h2 := by simpa using (measurable_pi_apply (a := i + 2)))
    (h3 := by simpa using (measurable_pi_apply (a := i + 3)))

private lemma misFromWeak_shift (x : ℤ → Fin 2) :
    misFromWeak (FiniteDependence.Coloring.shift (q := 2) x)
      = FiniteDependence.Coloring.shift (q := 2) (misFromWeak x) := by
  ext i
  simp [misFromWeak, FiniteDependence.Coloring.shift, FiniteDependence.shift,
    add_assoc, add_left_comm, add_comm]

private def goodTriple (a b c : Fin 2) : Prop :=
  ¬(a = 0 ∧ b = 0 ∧ c = 0) ∧ ¬(a = 1 ∧ b = 1 ∧ c = 1)

private instance decGoodTriple (a b c : Fin 2) : Decidable (goodTriple a b c) := by
  unfold goodTriple
  infer_instance

private lemma mis_no11_local :
    ∀ a b c d e : Fin 2,
      goodTriple a b c → goodTriple b c d → goodTriple c d e →
        ¬(misFactor4 a b c d = 1 ∧ misFactor4 b c d e = 1) := by
  decide

private lemma mis_no000_local :
    ∀ a b c d e f : Fin 2,
      goodTriple a b c → goodTriple b c d → goodTriple c d e → goodTriple d e f →
        ¬(misFactor4 a b c d = 0 ∧ misFactor4 b c d e = 0 ∧ misFactor4 c d e f = 0) := by
  decide

private lemma goodTriple_of_isWeak (x : ℤ → Fin 2) (hx : IsWeakTwoColoring x) (i : ℤ) :
    goodTriple (x i) (x (i + 1)) (x (i + 2)) := by
  rcases hx with ⟨h000, h111⟩
  exact ⟨h000 i, h111 i⟩

private lemma misFromWeak_isMIS_of_isWeak (x : ℤ → Fin 2) (hx : IsWeakTwoColoring x) :
    IsMIS (misFromWeak x) := by
  refine ⟨?_, ?_⟩
  · intro i hi
    rcases hi with ⟨h0, h1⟩
    have hgt0 : goodTriple (x i) (x (i + 1)) (x (i + 2)) := goodTriple_of_isWeak x hx i
    have hgt1 : goodTriple (x (i + 1)) (x (i + 2)) (x (i + 3)) := by
      simpa [add_assoc] using (goodTriple_of_isWeak x hx (i + 1))
    have hgt2 : goodTriple (x (i + 2)) (x (i + 3)) (x (i + 4)) := by
      simpa [add_assoc] using (goodTriple_of_isWeak x hx (i + 2))
    have hloc := mis_no11_local
      (a := x i) (b := x (i + 1)) (c := x (i + 2)) (d := x (i + 3)) (e := x (i + 4))
      hgt0 hgt1 hgt2
    have hm0 : misFactor4 (x i) (x (i + 1)) (x (i + 2)) (x (i + 3)) = 1 := by
      simpa [misFromWeak] using h0
    have hm1 : misFactor4 (x (i + 1)) (x (i + 2)) (x (i + 3)) (x (i + 4)) = 1 := by
      simpa [misFromWeak, add_assoc] using h1
    exact hloc ⟨hm0, hm1⟩
  · intro i hi
    rcases hi with ⟨h0, h1, h2⟩
    have hgt0 : goodTriple (x i) (x (i + 1)) (x (i + 2)) := goodTriple_of_isWeak x hx i
    have hgt1 : goodTriple (x (i + 1)) (x (i + 2)) (x (i + 3)) := by
      simpa [add_assoc] using (goodTriple_of_isWeak x hx (i + 1))
    have hgt2 : goodTriple (x (i + 2)) (x (i + 3)) (x (i + 4)) := by
      simpa [add_assoc] using (goodTriple_of_isWeak x hx (i + 2))
    have hgt3 : goodTriple (x (i + 3)) (x (i + 4)) (x (i + 5)) := by
      simpa [add_assoc] using (goodTriple_of_isWeak x hx (i + 3))
    have hloc := mis_no000_local
      (a := x i) (b := x (i + 1)) (c := x (i + 2)) (d := x (i + 3))
      (e := x (i + 4)) (f := x (i + 5)) hgt0 hgt1 hgt2 hgt3
    have hm0 : misFactor4 (x i) (x (i + 1)) (x (i + 2)) (x (i + 3)) = 0 := by
      simpa [misFromWeak] using h0
    have hm1 : misFactor4 (x (i + 1)) (x (i + 2)) (x (i + 3)) (x (i + 4)) = 0 := by
      simpa [misFromWeak, add_assoc] using h1
    have hm2 : misFactor4 (x (i + 2)) (x (i + 3)) (x (i + 4)) (x (i + 5)) = 0 := by
      simpa [misFromWeak, add_assoc] using h2
    exact hloc ⟨hm0, hm1, hm2⟩

private lemma comap_past_le_mis (i : ℤ) :
    (FiniteDependence.Coloring.pastMeasurableSpace (q := 2) i).comap misFromWeak
      ≤ FiniteDependence.Coloring.pastMeasurableSpace (q := 2) (i + 3) := by
  classical
  unfold FiniteDependence.Coloring.pastMeasurableSpace FiniteDependence.pastMeasurableSpace
  simp [MeasurableSpace.comap_iSup, MeasurableSpace.comap_comp]
  intro a ha
  have h0 : a < i + 3 := by linarith [ha]
  have h1 : a + 1 < i + 3 := by linarith [ha]
  have h2 : a + 2 < i + 3 := by linarith [ha]
  have h3 : a + 3 < i + 3 := by linarith [ha]
  have hm0 : Measurable[FiniteDependence.Coloring.pastMeasurableSpace (q := 2) (i + 3)]
      fun x : ℤ → Fin 2 => x a :=
    measurable_apply_past (q := 2) (i := i + 3) (j := a) h0
  have hm1 : Measurable[FiniteDependence.Coloring.pastMeasurableSpace (q := 2) (i + 3)]
      fun x : ℤ → Fin 2 => x (a + 1) :=
    measurable_apply_past (q := 2) (i := i + 3) (j := a + 1) h1
  have hm2 : Measurable[FiniteDependence.Coloring.pastMeasurableSpace (q := 2) (i + 3)]
      fun x : ℤ → Fin 2 => x (a + 2) :=
    measurable_apply_past (q := 2) (i := i + 3) (j := a + 2) h2
  have hm3 : Measurable[FiniteDependence.Coloring.pastMeasurableSpace (q := 2) (i + 3)]
      fun x : ℤ → Fin 2 => x (a + 3) :=
    measurable_apply_past (q := 2) (i := i + 3) (j := a + 3) h3
  have hmeas :
      Measurable[FiniteDependence.Coloring.pastMeasurableSpace (q := 2) (i + 3)]
        fun x : ℤ → Fin 2 => misFromWeak x a :=
    measurable_misFromWeak_at
      (m := FiniteDependence.Coloring.pastMeasurableSpace (q := 2) (i + 3)) (i := a)
      (h0 := hm0) (h1 := hm1) (h2 := hm2) (h3 := hm3)
  simpa [Function.comp] using hmeas.comap_le

private lemma comap_future_le_mis (i : ℤ) :
    (FiniteDependence.Coloring.futureMeasurableSpace (q := 2) i 5).comap misFromWeak
      ≤ FiniteDependence.Coloring.futureMeasurableSpace (q := 2) (i + 3) 2 := by
  classical
  unfold FiniteDependence.Coloring.futureMeasurableSpace FiniteDependence.futureMeasurableSpace
  simp [MeasurableSpace.comap_iSup, MeasurableSpace.comap_comp]
  intro a ha
  have h0 : i + 3 + 2 ≤ a := by linarith [ha]
  have h1 : i + 3 + 2 ≤ a + 1 := by linarith [ha]
  have h2 : i + 3 + 2 ≤ a + 2 := by linarith [ha]
  have h3 : i + 3 + 2 ≤ a + 3 := by linarith [ha]
  have hm0 : Measurable[FiniteDependence.Coloring.futureMeasurableSpace (q := 2) (i + 3) 2]
      fun x : ℤ → Fin 2 => x a :=
    measurable_apply_future (q := 2) (i := i + 3) (k := 2) (j := a) h0
  have hm1 : Measurable[FiniteDependence.Coloring.futureMeasurableSpace (q := 2) (i + 3) 2]
      fun x : ℤ → Fin 2 => x (a + 1) :=
    measurable_apply_future (q := 2) (i := i + 3) (k := 2) (j := a + 1) h1
  have hm2 : Measurable[FiniteDependence.Coloring.futureMeasurableSpace (q := 2) (i + 3) 2]
      fun x : ℤ → Fin 2 => x (a + 2) :=
    measurable_apply_future (q := 2) (i := i + 3) (k := 2) (j := a + 2) h2
  have hm3 : Measurable[FiniteDependence.Coloring.futureMeasurableSpace (q := 2) (i + 3) 2]
      fun x : ℤ → Fin 2 => x (a + 3) :=
    measurable_apply_future (q := 2) (i := i + 3) (k := 2) (j := a + 3) h3
  have hmeas :
      Measurable[FiniteDependence.Coloring.futureMeasurableSpace (q := 2) (i + 3) 2]
        fun x : ℤ → Fin 2 => misFromWeak x a :=
    measurable_misFromWeak_at
      (m := FiniteDependence.Coloring.futureMeasurableSpace (q := 2) (i + 3) 2) (i := a)
      (h0 := hm0) (h1 := hm1) (h2 := hm2) (h3 := hm3)
  simpa [Function.comp] using hmeas.comap_le

/-! ## Non-existence at dependence range 2 -/

/-- No stationary `2`-dependent weak-2-coloring law exists on `ℤ`. -/
theorem not_exists_stationary_twoDependent_weakTwoColoring :
    ¬ ExistsStationaryKDependentWeakTwoColoring 2 := by
  intro h
  rcases h with ⟨μ, hμ⟩
  rcases hμ with ⟨hstat, hdep, hweak⟩
  let μMIS : ProbabilityMeasure (ℤ → Fin 2) := μ.map measurable_misFromWeak.aemeasurable
  have hstatMIS : IsStationary μMIS := by
    have hcomm :
        (FiniteDependence.Coloring.shift (q := 2)) ∘ misFromWeak
          = misFromWeak ∘ (FiniteDependence.Coloring.shift (q := 2)) := by
      funext x
      simpa [Function.comp] using (misFromWeak_shift x).symm
    have hmeas_shift : Measurable (FiniteDependence.Coloring.shift (q := 2)) := measurable_shift 2
    change (((μMIS : ProbabilityMeasure (ℤ → Fin 2)) : Measure (ℤ → Fin 2)).map
      (FiniteDependence.Coloring.shift (q := 2)))
      = ((μMIS : ProbabilityMeasure (ℤ → Fin 2)) : Measure (ℤ → Fin 2))
    have hstat' :
        ((μ : Measure (ℤ → Fin 2)).map (FiniteDependence.Coloring.shift (q := 2)))
          = (μ : Measure (ℤ → Fin 2)) := hstat
    calc
      (((μMIS : ProbabilityMeasure (ℤ → Fin 2)) : Measure (ℤ → Fin 2)).map
          (FiniteDependence.Coloring.shift (q := 2)))
          = (((μ : Measure (ℤ → Fin 2)).map misFromWeak).map
              (FiniteDependence.Coloring.shift (q := 2))) := by
              rfl
      _ = (μ : Measure (ℤ → Fin 2)).map ((FiniteDependence.Coloring.shift (q := 2)) ∘ misFromWeak) := by
            simpa using (Measure.map_map (μ := (μ : Measure (ℤ → Fin 2))) hmeas_shift measurable_misFromWeak)
      _ = (μ : Measure (ℤ → Fin 2)).map (misFromWeak ∘ (FiniteDependence.Coloring.shift (q := 2))) := by
            simp [hcomm]
      _ = (((μ : Measure (ℤ → Fin 2)).map (FiniteDependence.Coloring.shift (q := 2))).map misFromWeak) := by
            symm
            simpa using (Measure.map_map (μ := (μ : Measure (ℤ → Fin 2))) measurable_misFromWeak hmeas_shift)
      _ = (μ : Measure (ℤ → Fin 2)).map misFromWeak := by
            simp [hstat']
      _ = ((μMIS : ProbabilityMeasure (ℤ → Fin 2)) : Measure (ℤ → Fin 2)) := rfl
  have hdep2 : FiniteDependence.Coloring.IsKDependent (q := 2) μ 2 := by
    simpa [IsKDependentCut, FiniteDependence.Coloring.IsKDependent] using hdep
  have hdepMIS : IsKDependentCut μMIS 5 := by
    have hkdepMap : FiniteDependence.Coloring.IsKDependent (q := 2) μMIS 5 := by
      intro i
      have hbase :
          Indep (FiniteDependence.Coloring.pastMeasurableSpace (q := 2) (i + 3))
            (FiniteDependence.Coloring.futureMeasurableSpace (q := 2) (i + 3) 2)
            (μ := (μ : Measure (ℤ → Fin 2))) := hdep2 (i + 3)
      have hcomap :
          Indep ((FiniteDependence.Coloring.pastMeasurableSpace (q := 2) i).comap misFromWeak)
            ((FiniteDependence.Coloring.futureMeasurableSpace (q := 2) i 5).comap misFromWeak)
              (μ := (μ : Measure (ℤ → Fin 2))) := by
        have h1 :
            Indep ((FiniteDependence.Coloring.pastMeasurableSpace (q := 2) i).comap misFromWeak)
              (FiniteDependence.Coloring.futureMeasurableSpace (q := 2) (i + 3) 2)
                (μ := (μ : Measure (ℤ → Fin 2))) :=
          indep_of_indep_of_le_left hbase (comap_past_le_mis (i := i))
        exact indep_of_indep_of_le_right h1 (comap_future_le_mis (i := i))
      have hmap :
          Indep (FiniteDependence.Coloring.pastMeasurableSpace (q := 2) i)
            (FiniteDependence.Coloring.futureMeasurableSpace (q := 2) i 5)
            (μ :=
              @Measure.map (ℤ → Fin 2) (ℤ → Fin 2) MeasurableSpace.pi MeasurableSpace.pi misFromWeak
                (μ : Measure (ℤ → Fin 2))) := by
        refine
          indep_map_of_indep_comap (mΩ' := (MeasurableSpace.pi : MeasurableSpace (ℤ → Fin 2)))
            (μ := (μ : Measure (ℤ → Fin 2))) (f := misFromWeak)
            (hf := measurable_misFromWeak.aemeasurable) (hm₁ := ?_) (hm₂ := ?_) hcomap
        · simpa using pastMeasurableSpace_le (q := 2) i
        · simpa using futureMeasurableSpace_le (q := 2) i 5
      simpa [μMIS, ProbabilityMeasure.map] using hmap
    simpa [IsKDependentCut, FiniteDependence.Coloring.IsKDependent] using hkdepMap
  have hMISsupport :
      ((μMIS : Measure (ℤ → Fin 2)) {x : ℤ → Fin 2 | IsMIS x} = 1) := by
    have hsub : {x : ℤ → Fin 2 | IsWeakTwoColoring x} ⊆ misFromWeak ⁻¹' {x : ℤ → Fin 2 | IsMIS x} := by
      intro x hx
      exact misFromWeak_isMIS_of_isWeak x hx
    have hpre :
        (μ : Measure (ℤ → Fin 2)) (misFromWeak ⁻¹' {x : ℤ → Fin 2 | IsMIS x}) = 1 := by
      have hle :
          (μ : Measure (ℤ → Fin 2)) {x : ℤ → Fin 2 | IsWeakTwoColoring x}
            ≤ (μ : Measure (ℤ → Fin 2)) (misFromWeak ⁻¹' {x : ℤ → Fin 2 | IsMIS x}) :=
        measure_mono hsub
      have hle1 :
          (μ : Measure (ℤ → Fin 2)) (misFromWeak ⁻¹' {x : ℤ → Fin 2 | IsMIS x}) ≤ 1 := by
        have : (μ : Measure (ℤ → Fin 2)) (misFromWeak ⁻¹' {x : ℤ → Fin 2 | IsMIS x})
            ≤ (μ : Measure (ℤ → Fin 2)) Set.univ := measure_mono (subset_univ _)
        simpa using this
      have hge : (1 : ENNReal) ≤
          (μ : Measure (ℤ → Fin 2)) (misFromWeak ⁻¹' {x : ℤ → Fin 2 | IsMIS x}) := by
        simpa [hweak] using hle
      exact le_antisymm hle1 hge
    have hmap :
        (μMIS : Measure (ℤ → Fin 2)) {x : ℤ → Fin 2 | IsMIS x}
          = (μ : Measure (ℤ → Fin 2)) (misFromWeak ⁻¹' {x : ℤ → Fin 2 | IsMIS x}) := by
      simpa [μMIS] using
        (ProbabilityMeasure.map_apply' μ measurable_misFromWeak.aemeasurable
          FiniteDependence.measurableSet_isMIS)
    exact hmap.trans hpre
  have hexMIS5 : ExistsStationaryKDependentMIS 5 := by
    refine ⟨μMIS, ?_⟩
    exact ⟨hstatMIS, hdepMIS, hMISsupport⟩
  exact LowerBoundBridge.not_exists_stationary_fiveDependent_MIS hexMIS5

/--
No stationary `1`-dependent proper `3`-coloring exists on `ℤ`.

Proof idea: the ascent factor `Y_i = 1{C_i < C_{i+1}}` turns such a process into a stationary
`2`-dependent weak-2-coloring, contradicting
`not_exists_stationary_twoDependent_weakTwoColoring`.
-/
theorem not_exists_stationary_oneDependent_threeColoring :
    ¬ ∃ μ : ProbabilityMeasure (ℤ → Fin 3),
        IsStationary μ ∧
        IsKDependentCut μ 1 ∧
        (μ : Measure (ℤ → Fin 3)) {x | IsColoring (q := 3) x} = 1 := by
  intro h
  rcases h with ⟨μ3, hstat3, hdep1, hcol3⟩
  let μ2 : ProbabilityMeasure (ℤ → Fin 2) := μ3.map measurable_weakTwoFromThree.aemeasurable

  have hdep1' : FiniteDependence.Coloring.IsKDependent (q := 3) μ3 1 := by
    simpa [IsKDependentCut, FiniteDependence.Coloring.IsKDependent] using hdep1

  have hstat2 : IsStationary μ2 := by
    have hcomm :
        (FiniteDependence.Coloring.shift (q := 2)) ∘ weakTwoFromThree
          = weakTwoFromThree ∘ (FiniteDependence.Coloring.shift (q := 3)) := by
      funext c
      simpa [Function.comp] using (weakTwoFromThree_shift c).symm
    have hmeas_shift2 : Measurable (FiniteDependence.Coloring.shift (q := 2)) := measurable_shift 2
    have hmeas_shift3 : Measurable (FiniteDependence.Coloring.shift (q := 3)) := measurable_shift 3
    change ((μ2 : Measure (ℤ → Fin 2)).map (FiniteDependence.Coloring.shift (q := 2)))
      = (μ2 : Measure (ℤ → Fin 2))
    have hstat3' :
        ((μ3 : Measure (ℤ → Fin 3)).map (FiniteDependence.Coloring.shift (q := 3)))
          = (μ3 : Measure (ℤ → Fin 3)) := by
      simpa [IsStationary, FiniteDependence.Coloring.IsStationary] using hstat3
    calc
      ((μ2 : Measure (ℤ → Fin 2)).map (FiniteDependence.Coloring.shift (q := 2)))
          = (((μ3 : Measure (ℤ → Fin 3)).map weakTwoFromThree).map
              (FiniteDependence.Coloring.shift (q := 2))) := by
              rfl
      _ = (μ3 : Measure (ℤ → Fin 3)).map ((FiniteDependence.Coloring.shift (q := 2)) ∘ weakTwoFromThree) := by
            simpa using (Measure.map_map (μ := (μ3 : Measure (ℤ → Fin 3))) hmeas_shift2
              measurable_weakTwoFromThree)
      _ = (μ3 : Measure (ℤ → Fin 3)).map (weakTwoFromThree ∘ (FiniteDependence.Coloring.shift (q := 3))) := by
            simp [hcomm]
      _ = (((μ3 : Measure (ℤ → Fin 3)).map (FiniteDependence.Coloring.shift (q := 3))).map weakTwoFromThree) := by
            symm
            simpa using (Measure.map_map (μ := (μ3 : Measure (ℤ → Fin 3))) measurable_weakTwoFromThree
              hmeas_shift3)
      _ = (μ3 : Measure (ℤ → Fin 3)).map weakTwoFromThree := by
            simp [hstat3']
      _ = (μ2 : Measure (ℤ → Fin 2)) := rfl

  have hdep2 : IsKDependentCut μ2 2 := by
    have hkdepMap : FiniteDependence.Coloring.IsKDependent (q := 2) μ2 2 := by
      intro i
      have hbase :
          Indep (FiniteDependence.Coloring.pastMeasurableSpace (q := 3) (i + 1))
            (FiniteDependence.Coloring.futureMeasurableSpace (q := 3) (i + 1) 1)
            (μ := (μ3 : Measure (ℤ → Fin 3))) := hdep1' (i + 1)
      have hcomap :
          Indep ((FiniteDependence.Coloring.pastMeasurableSpace (q := 2) i).comap weakTwoFromThree)
            ((FiniteDependence.Coloring.futureMeasurableSpace (q := 2) i 2).comap weakTwoFromThree)
              (μ := (μ3 : Measure (ℤ → Fin 3))) := by
        have h1 :
            Indep ((FiniteDependence.Coloring.pastMeasurableSpace (q := 2) i).comap weakTwoFromThree)
              (FiniteDependence.Coloring.futureMeasurableSpace (q := 3) (i + 1) 1)
                (μ := (μ3 : Measure (ℤ → Fin 3))) :=
          indep_of_indep_of_le_left hbase (comap_past_le_weak (i := i))
        exact indep_of_indep_of_le_right h1 (comap_future_le_weak_k2 (i := i))
      have hmap :
          Indep (FiniteDependence.Coloring.pastMeasurableSpace (q := 2) i)
            (FiniteDependence.Coloring.futureMeasurableSpace (q := 2) i 2)
            (μ :=
              @Measure.map (ℤ → Fin 3) (ℤ → Fin 2) MeasurableSpace.pi MeasurableSpace.pi weakTwoFromThree
                (μ3 : Measure (ℤ → Fin 3))) := by
        refine
          indep_map_of_indep_comap (mΩ' := (MeasurableSpace.pi : MeasurableSpace (ℤ → Fin 2)))
            (μ := (μ3 : Measure (ℤ → Fin 3))) (f := weakTwoFromThree)
            (hf := measurable_weakTwoFromThree.aemeasurable) (hm₁ := ?_) (hm₂ := ?_) hcomap
        · simpa using pastMeasurableSpace_le (q := 2) i
        · simpa using futureMeasurableSpace_le (q := 2) i 2
      simpa [μ2, ProbabilityMeasure.map] using hmap
    simpa [IsKDependentCut, FiniteDependence.Coloring.IsKDependent] using hkdepMap

  have hweak2 :
      ((μ2 : Measure (ℤ → Fin 2)) {x : ℤ → Fin 2 | IsWeakTwoColoring x} = 1) := by
    have hpre :
        (μ3 : Measure (ℤ → Fin 3)) (weakTwoFromThree ⁻¹' {x : ℤ → Fin 2 | IsWeakTwoColoring x}) = 1 := by
      have hsub :
          {c : ℤ → Fin 3 | IsColoring (q := 3) c}
            ⊆ weakTwoFromThree ⁻¹' {x : ℤ → Fin 2 | IsWeakTwoColoring x} := by
        intro c hc
        exact weakTwoFromThree_isWeak_of_isColoring c hc
      have hle :
          (μ3 : Measure (ℤ → Fin 3)) {c : ℤ → Fin 3 | IsColoring (q := 3) c}
            ≤ (μ3 : Measure (ℤ → Fin 3))
                (weakTwoFromThree ⁻¹' {x : ℤ → Fin 2 | IsWeakTwoColoring x}) :=
        measure_mono hsub
      have hle1 :
          (μ3 : Measure (ℤ → Fin 3)) (weakTwoFromThree ⁻¹' {x : ℤ → Fin 2 | IsWeakTwoColoring x}) ≤ 1 := by
        have : (μ3 : Measure (ℤ → Fin 3))
            (weakTwoFromThree ⁻¹' {x : ℤ → Fin 2 | IsWeakTwoColoring x})
              ≤ (μ3 : Measure (ℤ → Fin 3)) Set.univ := measure_mono (subset_univ _)
        simpa using this
      have hge : (1 : ENNReal) ≤
          (μ3 : Measure (ℤ → Fin 3)) (weakTwoFromThree ⁻¹' {x : ℤ → Fin 2 | IsWeakTwoColoring x}) := by
        simpa [hcol3] using hle
      exact le_antisymm hle1 hge
    have hmap :
        (μ2 : Measure (ℤ → Fin 2)) {x : ℤ → Fin 2 | IsWeakTwoColoring x}
          = (μ3 : Measure (ℤ → Fin 3)) (weakTwoFromThree ⁻¹' {x : ℤ → Fin 2 | IsWeakTwoColoring x}) := by
      simpa [μ2] using
        (ProbabilityMeasure.map_apply' μ3 measurable_weakTwoFromThree.aemeasurable
          FiniteDependence.measurableSet_isWeakTwoColoring)
    exact hmap.trans hpre

  have hexWeak2 : ExistsStationaryKDependentWeakTwoColoring 2 := by
    refine ⟨μ2, ?_⟩
    exact ⟨hstat2, hdep2, hweak2⟩

  exact not_exists_stationary_twoDependent_weakTwoColoring hexWeak2

end WeakTwo

end FiniteDependence
