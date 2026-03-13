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

/-- If every output coordinate of a factor is measurable from a fixed family of source coordinates
whose offsets are bounded above by `r`, then the target past σ-algebra at `i` pulls back into the
source past σ-algebra at `i + r`. -/
lemma comap_past_le_of_local {ι : Type*} {q q' : ℕ}
    {f : (ℤ → Fin q) → (ℤ → Fin q')} (o : ι → ℤ) (r : ℤ)
    (hlocal : ∀ {m : MeasurableSpace (ℤ → Fin q)} (a : ℤ),
      (∀ t, Measurable[m] fun x : ℤ → Fin q => x (a + o t)) →
        Measurable[m] fun x : ℤ → Fin q => f x a)
    (hupper : ∀ t, o t ≤ r) (i : ℤ) :
    (FiniteDependence.Coloring.pastMeasurableSpace (q := q') i).comap f
      ≤ FiniteDependence.Coloring.pastMeasurableSpace (q := q) (i + r) := by
  classical
  unfold FiniteDependence.Coloring.pastMeasurableSpace FiniteDependence.pastMeasurableSpace
  simp [MeasurableSpace.comap_iSup, MeasurableSpace.comap_comp]
  intro a ha
  have hcoords :
      ∀ t, Measurable[FiniteDependence.Coloring.pastMeasurableSpace (q := q) (i + r)]
        fun x : ℤ → Fin q => x (a + o t) := by
    intro t
    refine measurable_apply_past (q := q) (i := i + r) (j := a + o t) ?_
    linarith [ha, hupper t]
  have hmeas :
      Measurable[FiniteDependence.Coloring.pastMeasurableSpace (q := q) (i + r)]
        fun x : ℤ → Fin q => f x a :=
    hlocal (m := FiniteDependence.Coloring.pastMeasurableSpace (q := q) (i + r)) a hcoords
  simpa [Function.comp] using hmeas.comap_le

/-- If every output coordinate of a factor is measurable from a fixed family of source coordinates
and each offset lies far enough to the future relative to a source cut, then the target future
σ-algebra at `(i, k')` pulls back into the source future σ-algebra at `(i + r, k)`. -/
lemma comap_future_le_of_local {ι : Type*} {q q' : ℕ}
    {f : (ℤ → Fin q) → (ℤ → Fin q')} (o : ι → ℤ) (r : ℤ) (k k' : ℕ)
    (hlocal : ∀ {m : MeasurableSpace (ℤ → Fin q)} (a : ℤ),
      (∀ t, Measurable[m] fun x : ℤ → Fin q => x (a + o t)) →
        Measurable[m] fun x : ℤ → Fin q => f x a)
    (hlower : ∀ t, r + (k : ℤ) ≤ (k' : ℤ) + o t) (i : ℤ) :
    (FiniteDependence.Coloring.futureMeasurableSpace (q := q') i k').comap f
      ≤ FiniteDependence.Coloring.futureMeasurableSpace (q := q) (i + r) k := by
  classical
  unfold FiniteDependence.Coloring.futureMeasurableSpace FiniteDependence.futureMeasurableSpace
  simp [MeasurableSpace.comap_iSup, MeasurableSpace.comap_comp]
  intro a ha
  have hcoords :
      ∀ t, Measurable[FiniteDependence.Coloring.futureMeasurableSpace (q := q) (i + r) k]
        fun x : ℤ → Fin q => x (a + o t) := by
    intro t
    refine measurable_apply_future (q := q) (i := i + r) (k := k) (j := a + o t) ?_
    linarith [ha, hlower t]
  have hmeas :
      Measurable[FiniteDependence.Coloring.futureMeasurableSpace (q := q) (i + r) k]
        fun x : ℤ → Fin q => f x a :=
    hlocal (m := FiniteDependence.Coloring.futureMeasurableSpace (q := q) (i + r) k) a hcoords
  simpa [Function.comp] using hmeas.comap_le

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

/-- A shift-commuting measurable factor preserves stationarity. -/
lemma isStationary_map_of_comm {q q' : ℕ}
    {μ : ProbabilityMeasure (ℤ → Fin q)} {f : (ℤ → Fin q) → (ℤ → Fin q')}
    (hf : Measurable f)
    (hcomm : (FiniteDependence.Coloring.shift (q := q') ∘ f)
      = (f ∘ FiniteDependence.Coloring.shift (q := q)))
    (hstat : FiniteDependence.Coloring.IsStationary (q := q) μ) :
    FiniteDependence.Coloring.IsStationary (q := q') (μ.map hf.aemeasurable) := by
  change
      (((μ.map hf.aemeasurable : ProbabilityMeasure (ℤ → Fin q')) : Measure (ℤ → Fin q')).map
        (FiniteDependence.Coloring.shift (q := q'))
        = ((μ.map hf.aemeasurable : ProbabilityMeasure (ℤ → Fin q')) : Measure (ℤ → Fin q')))
  have hstat' :
      ((μ : Measure (ℤ → Fin q)).map (FiniteDependence.Coloring.shift (q := q)))
        = (μ : Measure (ℤ → Fin q)) := hstat
  calc
    (((μ.map hf.aemeasurable : ProbabilityMeasure (ℤ → Fin q')) : Measure (ℤ → Fin q')).map
        (FiniteDependence.Coloring.shift (q := q')))
        = (((μ : Measure (ℤ → Fin q)).map f).map (FiniteDependence.Coloring.shift (q := q'))) := by
            rfl
    _ = (μ : Measure (ℤ → Fin q)).map
          ((FiniteDependence.Coloring.shift (q := q')) ∘ f) := by
            rw [Measure.map_map (measurable_shift q') hf]
    _ = (μ : Measure (ℤ → Fin q)).map
          (f ∘ FiniteDependence.Coloring.shift (q := q)) := by
            simp [hcomm]
    _ = (((μ : Measure (ℤ → Fin q)).map (FiniteDependence.Coloring.shift (q := q))).map f) := by
          symm
          rw [Measure.map_map hf (measurable_shift q)]
    _ = (μ : Measure (ℤ → Fin q)).map f := by
          simp [hstat']
    _ = ((μ.map hf.aemeasurable : ProbabilityMeasure (ℤ → Fin q')) : Measure (ℤ → Fin q')) := by
          rfl

/-- A measurable factor preserves cut-form finite dependence once its past/future comaps fit
inside the source past/future σ-algebras at each cut. -/
lemma isKDependent_map_of_past_future {q q' k k' : ℕ}
    {μ : ProbabilityMeasure (ℤ → Fin q)} {f : (ℤ → Fin q) → (ℤ → Fin q')}
    (hf : AEMeasurable f (μ : Measure (ℤ → Fin q)))
    (hdep : FiniteDependence.Coloring.IsKDependent (q := q) μ k)
    (cut : ℤ → ℤ)
    (hpast : ∀ i,
      (FiniteDependence.Coloring.pastMeasurableSpace (q := q') i).comap f
        ≤ FiniteDependence.Coloring.pastMeasurableSpace (q := q) (cut i))
    (hfuture : ∀ i,
      (FiniteDependence.Coloring.futureMeasurableSpace (q := q') i k').comap f
        ≤ FiniteDependence.Coloring.futureMeasurableSpace (q := q) (cut i) k) :
    FiniteDependence.Coloring.IsKDependent (q := q') (μ.map hf) k' := by
  intro i
  have hbase :
      Indep (FiniteDependence.Coloring.pastMeasurableSpace (q := q) (cut i))
        (FiniteDependence.Coloring.futureMeasurableSpace (q := q) (cut i) k)
        (μ := (μ : Measure (ℤ → Fin q))) := hdep (cut i)
  have hcomap :
      Indep ((FiniteDependence.Coloring.pastMeasurableSpace (q := q') i).comap f)
        ((FiniteDependence.Coloring.futureMeasurableSpace (q := q') i k').comap f)
        (μ := (μ : Measure (ℤ → Fin q))) := by
    have h1 :
        Indep ((FiniteDependence.Coloring.pastMeasurableSpace (q := q') i).comap f)
          (FiniteDependence.Coloring.futureMeasurableSpace (q := q) (cut i) k)
          (μ := (μ : Measure (ℤ → Fin q))) :=
      indep_of_indep_of_le_left hbase (hpast i)
    exact indep_of_indep_of_le_right h1 (hfuture i)
  have hmap :
      Indep (FiniteDependence.Coloring.pastMeasurableSpace (q := q') i)
        (FiniteDependence.Coloring.futureMeasurableSpace (q := q') i k')
        (μ :=
          @Measure.map (ℤ → Fin q) (ℤ → Fin q') MeasurableSpace.pi MeasurableSpace.pi f
            (μ : Measure (ℤ → Fin q))) := by
    refine
      indep_map_of_indep_comap (mΩ' := (MeasurableSpace.pi : MeasurableSpace (ℤ → Fin q')))
        (μ := (μ : Measure (ℤ → Fin q))) (f := f) (hf := hf) (hm₁ := ?_) (hm₂ := ?_) hcomap
    · simpa using pastMeasurableSpace_le q' i
    · simpa using futureMeasurableSpace_le q' i k'
  simpa [ProbabilityMeasure.map] using hmap

end FiniteDependence.Coloring
