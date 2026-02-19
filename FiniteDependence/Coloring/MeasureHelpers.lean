import FiniteDependence.Coloring.ColoringProcess

import Mathlib.MeasureTheory.Measure.Map
import Mathlib.MeasureTheory.MeasurableSpace.Prod

/-!
# Shared measurability and independence helpers for coloring processes

This module centralizes routine lemmas used when transporting finite-dependence
statements through measurable local factors.
-/

namespace FiniteDependence.Coloring

open MeasureTheory ProbabilityTheory

/-- Measurability of the shift map on `Fin q`-valued configurations. -/
lemma measurable_shift (q : ℕ) : Measurable (FiniteDependence.Coloring.shift (q := q)) := by
  simpa [FiniteDependence.Coloring.shift] using (FiniteDependence.measurable_shift (α := Fin q))

/-- Coordinate projection measurability in the past σ-algebra. -/
lemma measurable_apply_past {q : ℕ} (i j : ℤ) (hj : j < i) :
    Measurable[FiniteDependence.Coloring.pastMeasurableSpace (q := q) i] fun x : ℤ → Fin q => x j := by
  refine (Measurable.of_comap_le
    (m₁ := FiniteDependence.Coloring.pastMeasurableSpace (q := q) i) (m₂ := inferInstance) ?_)
  simpa [FiniteDependence.Coloring.pastMeasurableSpace, FiniteDependence.pastMeasurableSpace] using
    (le_iSup (fun j' : {j : ℤ // j < i} =>
      MeasurableSpace.comap (fun x : ℤ → Fin q => x j'.1) inferInstance) ⟨j, hj⟩)

/-- Coordinate projection measurability in the future σ-algebra. -/
lemma measurable_apply_future {q : ℕ} (i : ℤ) (k : ℕ) (j : ℤ) (hj : i + k ≤ j) :
    Measurable[FiniteDependence.Coloring.futureMeasurableSpace (q := q) i k] fun x : ℤ → Fin q => x j := by
  refine (Measurable.of_comap_le
    (m₁ := FiniteDependence.Coloring.futureMeasurableSpace (q := q) i k) (m₂ := inferInstance) ?_)
  simpa [FiniteDependence.Coloring.futureMeasurableSpace, FiniteDependence.futureMeasurableSpace] using
    (le_iSup (fun j' : {j : ℤ // i + k ≤ j} =>
      MeasurableSpace.comap (fun x : ℤ → Fin q => x j'.1) inferInstance) ⟨j, hj⟩)

/-- The past coordinate σ-algebra is below the ambient product σ-algebra. -/
lemma pastMeasurableSpace_le (q : ℕ) (i : ℤ) :
    FiniteDependence.Coloring.pastMeasurableSpace (q := q) i
      ≤ (MeasurableSpace.pi : MeasurableSpace (ℤ → Fin q)) := by
  classical
  unfold FiniteDependence.Coloring.pastMeasurableSpace FiniteDependence.pastMeasurableSpace
  refine iSup_le ?_
  intro j
  have hmeas : Measurable fun x : ℤ → Fin q => x j.1 := by
    simpa using (measurable_pi_apply (a := j.1))
  simpa using hmeas.comap_le

/-- The future coordinate σ-algebra is below the ambient product σ-algebra. -/
lemma futureMeasurableSpace_le (q : ℕ) (i : ℤ) (k : ℕ) :
    FiniteDependence.Coloring.futureMeasurableSpace (q := q) i k
      ≤ (MeasurableSpace.pi : MeasurableSpace (ℤ → Fin q)) := by
  classical
  unfold FiniteDependence.Coloring.futureMeasurableSpace FiniteDependence.futureMeasurableSpace
  refine iSup_le ?_
  intro j
  have hmeas : Measurable fun x : ℤ → Fin q => x j.1 := by
    simpa using (measurable_pi_apply (a := j.1))
  simpa using hmeas.comap_le

/-- Pushes independence of comaps to independence on the mapped measure. -/
lemma indep_map_of_indep_comap {Ω Ω' : Type*} [MeasurableSpace Ω]
    (mΩ' : MeasurableSpace Ω') {μ : Measure Ω} {f : Ω → Ω'} (hf : AEMeasurable f μ)
    {m₁ m₂ : MeasurableSpace Ω'} (hm₁ : m₁ ≤ mΩ') (hm₂ : m₂ ≤ mΩ')
    (h : Indep (m₁.comap f) (m₂.comap f) μ) :
    Indep m₁ m₂ (@Measure.map Ω Ω' _ mΩ' f μ) := by
  classical
  refine (ProbabilityTheory.Indep_iff (m₁ := m₁) (m₂ := m₂) (μ := @Measure.map Ω Ω' _ mΩ' f μ)).2 ?_
  intro s t hs ht
  have hs' : MeasurableSet[mΩ'] s := hm₁ _ hs
  have ht' : MeasurableSet[mΩ'] t := hm₂ _ ht
  have hst' : MeasurableSet[mΩ'] (s ∩ t) := hs'.inter ht'
  have hs_pre : MeasurableSet[m₁.comap f] (f ⁻¹' s) := ⟨s, hs, rfl⟩
  have ht_pre : MeasurableSet[m₂.comap f] (f ⁻¹' t) := ⟨t, ht, rfl⟩
  have hpre : μ (f ⁻¹' (s ∩ t)) = μ (f ⁻¹' s) * μ (f ⁻¹' t) := by
    have hEq :=
      (ProbabilityTheory.Indep_iff (m₁ := m₁.comap f) (m₂ := m₂.comap f) (μ := μ)).1 h
    simpa [Set.preimage_inter] using hEq (f ⁻¹' s) (f ⁻¹' t) hs_pre ht_pre
  calc
    (@Measure.map Ω Ω' _ mΩ' f μ) (s ∩ t) = μ (f ⁻¹' (s ∩ t)) := by
      simpa using (Measure.map_apply_of_aemeasurable (μ := μ) (f := f) (mβ := mΩ') hf hst')
    _ = μ (f ⁻¹' s) * μ (f ⁻¹' t) := hpre
    _ = (@Measure.map Ω Ω' _ mΩ' f μ) s * (@Measure.map Ω Ω' _ mΩ' f μ) t := by
      simp [Measure.map_apply_of_aemeasurable (μ := μ) (f := f) (mβ := mΩ') hf hs',
        Measure.map_apply_of_aemeasurable (μ := μ) (f := f) (mβ := mΩ') hf ht']

end FiniteDependence.Coloring
