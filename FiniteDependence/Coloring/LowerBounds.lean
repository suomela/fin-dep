import FiniteDependence.Coloring.Existence

import Mathlib.MeasureTheory.Measure.Map
import Mathlib.MeasureTheory.MeasurableSpace.Prod

/-!
# Lower bounds for finitely dependent colorings on `ℤ`

This file contains non-existence statements complementary to
`FiniteDependence/Coloring/Existence.lean`.
-/

namespace FiniteDependence.Coloring

open MeasureTheory ProbabilityTheory Set

private lemma measurable_apply_past (i j : ℤ) (hj : j < i) :
    Measurable[pastMeasurableSpace (q := 4) i] fun x : ℤ → Fin 4 => x j := by
  refine (Measurable.of_comap_le
    (m₁ := pastMeasurableSpace (q := 4) i) (m₂ := inferInstance) ?_)
  simpa [pastMeasurableSpace, FiniteDependence.pastMeasurableSpace] using
    (le_iSup (fun j' : {j : ℤ // j < i} =>
      MeasurableSpace.comap (fun x : ℤ → Fin 4 => x j'.1) inferInstance) ⟨j, hj⟩)

private lemma measurable_apply_future (i : ℤ) (k : ℕ) (j : ℤ) (hj : i + k ≤ j) :
    Measurable[futureMeasurableSpace (q := 4) i k] fun x : ℤ → Fin 4 => x j := by
  refine (Measurable.of_comap_le
    (m₁ := futureMeasurableSpace (q := 4) i k) (m₂ := inferInstance) ?_)
  simpa [futureMeasurableSpace, FiniteDependence.futureMeasurableSpace] using
    (le_iSup (fun j' : {j : ℤ // i + k ≤ j} =>
      MeasurableSpace.comap (fun x : ℤ → Fin 4 => x j'.1) inferInstance) ⟨j, hj⟩)

private lemma measurableSet_isColoring :
    MeasurableSet ({x : ℤ → Fin 4 | IsColoring x} : Set (ℤ → Fin 4)) := by
  classical
  have hbad (i : ℤ) : MeasurableSet ({x : ℤ → Fin 4 | x i = x (i + 1)} : Set (ℤ → Fin 4)) := by
    have hsingle (a : Fin 4) :
        MeasurableSet ({x : ℤ → Fin 4 | x i = a ∧ x (i + 1) = a} : Set (ℤ → Fin 4)) := by
      have hmeas : Measurable (fun x : ℤ → Fin 4 => (x i, x (i + 1))) :=
        (measurable_pi_apply (a := i)).prodMk (measurable_pi_apply (a := i + 1))
      simpa [Set.preimage, Set.mem_singleton_iff] using
        (measurableSet_singleton (a, a)).preimage hmeas
    have hEq :
        ({x : ℤ → Fin 4 | x i = x (i + 1)} : Set (ℤ → Fin 4))
          = ⋃ a : Fin 4, ({x : ℤ → Fin 4 | x i = a ∧ x (i + 1) = a} : Set (ℤ → Fin 4)) := by
      ext x
      constructor
      · intro hx
        refine mem_iUnion.2 ?_
        refine ⟨x i, ?_⟩
        constructor
        · rfl
        · exact hx.symm
      · intro hx
        rcases mem_iUnion.1 hx with ⟨a, ha⟩
        exact ha.1.trans ha.2.symm
    simpa [hEq] using MeasurableSet.iUnion hsingle

  have hEq :
      ({x : ℤ → Fin 4 | IsColoring x} : Set (ℤ → Fin 4))
        = (⋃ i : ℤ, ({x : ℤ → Fin 4 | x i = x (i + 1)} : Set (ℤ → Fin 4)))ᶜ := by
    ext x
    simp [IsColoring]

  simpa [hEq] using (MeasurableSet.iUnion hbad).compl

/-- No stationary `0`-dependent proper `4`-coloring law exists on `ℤ`. -/
theorem not_exists_stationary_zeroDependent_fourColoring :
    ¬ ∃ μ : ProbabilityMeasure (ℤ → Fin 4),
        IsStationary μ ∧
        IsKDependent μ 0 ∧
        (μ : Measure (ℤ → Fin 4)) {x | IsColoring x} = 1 := by
  intro h
  rcases h with ⟨μ, hstat, hdep0, hcolor⟩

  let A : Fin 4 → Set (ℤ → Fin 4) := fun a => {x | x 0 = a}
  let B : Fin 4 → Set (ℤ → Fin 4) := fun a => {x | x 1 = a}
  let μm : Measure (ℤ → Fin 4) := (μ : Measure (ℤ → Fin 4))

  have hdep0' :
      FiniteDependence.IsKDependent (coord := fun x : ℤ → Fin 4 => x) (μ := μm) 0 := by
    simpa [μm, IsKDependent] using hdep0

  have hind :
      Indep
        (FiniteDependence.pastMeasurableSpace (coord := fun x : ℤ → Fin 4 => x) 1)
        (FiniteDependence.futureMeasurableSpace (coord := fun x : ℤ → Fin 4 => x) 1 0)
        (μ := μm) := by
    simpa using hdep0' 1

  have hA_meas (a : Fin 4) : MeasurableSet (A a) := by
    have hcoord : Measurable (fun x : ℤ → Fin 4 => x 0) := by
      simpa using (measurable_pi_apply (a := (0 : ℤ)))
    simpa [A, Set.preimage, Set.mem_singleton_iff] using (measurableSet_singleton a).preimage hcoord

  have hA_past (a : Fin 4) :
      MeasurableSet[FiniteDependence.pastMeasurableSpace (coord := fun x : ℤ → Fin 4 => x) 1] (A a) := by
    have hcoord :
        Measurable[FiniteDependence.pastMeasurableSpace (coord := fun x : ℤ → Fin 4 => x) 1]
          (fun x : ℤ → Fin 4 => x 0) :=
      measurable_apply_past (i := 1) (j := 0) (by decide)
    simpa [A, Set.preimage, Set.mem_singleton_iff] using (measurableSet_singleton a).preimage hcoord

  have hB_future (a : Fin 4) :
      MeasurableSet[FiniteDependence.futureMeasurableSpace (coord := fun x : ℤ → Fin 4 => x) 1 0] (B a) := by
    have hcoord :
        Measurable[FiniteDependence.futureMeasurableSpace (coord := fun x : ℤ → Fin 4 => x) 1 0]
          (fun x : ℤ → Fin 4 => x 1) :=
      measurable_apply_future (i := 1) (k := 0) (j := 1) (by decide)
    simpa [B, Set.preimage, Set.mem_singleton_iff] using (measurableSet_singleton a).preimage hcoord

  have hcolorMeas : MeasurableSet ({x : ℤ → Fin 4 | IsColoring x} : Set (ℤ → Fin 4)) :=
    measurableSet_isColoring

  have hcolorμm : μm ({x : ℤ → Fin 4 | IsColoring x} : Set (ℤ → Fin 4)) = 1 := by
    simpa [μm] using hcolor

  have hμuniv : μm Set.univ = 1 := by
    simpa [μm]

  have hcolorCompl :
      μm ({x : ℤ → Fin 4 | IsColoring x}ᶜ) = 0 := by
    calc
      μm ({x : ℤ → Fin 4 | IsColoring x}ᶜ)
          = μm Set.univ - μm ({x : ℤ → Fin 4 | IsColoring x} : Set (ℤ → Fin 4)) := by
            simpa using (measure_compl (μ := μm) hcolorMeas)
      _ = 1 - 1 := by simp [hcolorμm, hμuniv]
      _ = 0 := by simp

  have hAB_zero (a : Fin 4) :
      μm (A a ∩ B a) = 0 := by
    have hsub : A a ∩ B a ⊆ ({x : ℤ → Fin 4 | IsColoring x} : Set (ℤ → Fin 4))ᶜ := by
      intro x hx
      rcases hx with ⟨hx0, hx1⟩
      change x 0 = a at hx0
      change x 1 = a at hx1
      change ¬ IsColoring x
      intro hxcol
      exact (hxcol 0) (hx0.trans hx1.symm)
    have hle : μm (A a ∩ B a) ≤ μm ({x : ℤ → Fin 4 | IsColoring x}ᶜ) :=
      measure_mono hsub
    exact le_antisymm (by simpa [hcolorCompl] using hle) (by simp)

  have hB_eq_A (a : Fin 4) :
      μm (B a) = μm (A a) := by
    have hpre : B a = (FiniteDependence.shift (α := Fin 4)) ⁻¹' (A a) := by
      ext x
      simp [A, B, FiniteDependence.shift]
    calc
      μm (B a)
          = μm ((FiniteDependence.shift (α := Fin 4)) ⁻¹' (A a)) := by
              simpa [hpre]
      _ = (μm.map (FiniteDependence.shift (α := Fin 4))) (A a) := by
            symm
            exact Measure.map_apply (μ := μm) (f := FiniteDependence.shift (α := Fin 4))
              (FiniteDependence.measurable_shift (α := Fin 4)) (hA_meas a)
      _ = μm (A a) := by
            simpa [μm, IsStationary, FiniteDependence.IsStationary] using
              congrArg (fun ν : Measure (ℤ → Fin 4) => ν (A a)) hstat

  have hA_zero (a : Fin 4) : μm (A a) = 0 := by
    have hmul :
        μm (A a ∩ B a) = μm (A a) * μm (B a) := by
      exact (ProbabilityTheory.Indep_iff
        (m₁ := FiniteDependence.pastMeasurableSpace (coord := fun x : ℤ → Fin 4 => x) 1)
        (m₂ := FiniteDependence.futureMeasurableSpace (coord := fun x : ℤ → Fin 4 => x) 1 0)
        (μ := μm)).1 hind (A a) (B a) (hA_past a) (hB_future a)
    have hmul_zero : μm (A a) * μm (B a) = 0 := by
      calc
        μm (A a) * μm (B a) = μm (A a ∩ B a) := by simpa [hmul] using hmul.symm
        _ = 0 := hAB_zero a
    have hsq : μm (A a) * μm (A a) = 0 := by
      simpa [hB_eq_A a] using hmul_zero
    rcases mul_eq_zero.mp hsq with hzero | hzero
    · exact hzero
    · exact hzero

  let eval0 : (ℤ → Fin 4) → Fin 4 := fun x => x 0

  have hsum :
      (∑ a : Fin 4, μm (A a)) = μm Set.univ := by
    have hsum' :
        (∑ a ∈ (Finset.univ : Finset (Fin 4)),
            μm (eval0 ⁻¹' ({a} : Set (Fin 4))))
          = μm (eval0 ⁻¹' (↑(Finset.univ : Finset (Fin 4)) : Set (Fin 4))) := by
      refine sum_measure_preimage_singleton (μ := μm)
        (s := (Finset.univ : Finset (Fin 4))) (f := eval0) ?_
      intro a ha
      have hcoord : Measurable eval0 := by
        simpa [eval0] using (measurable_pi_apply (a := (0 : ℤ)))
      simpa [Set.preimage, Set.mem_singleton_iff] using (measurableSet_singleton a).preimage hcoord
    simpa [A, eval0] using hsum'

  have hsum_zero : (∑ a : Fin 4, μm (A a)) = 0 := by
    refine Finset.sum_eq_zero ?_
    intro a ha
    exact hA_zero a

  have hUnivZero : μm Set.univ = 0 := by
    simpa [hsum] using hsum_zero

  have hUnivOne : μm Set.univ = 1 := hμuniv

  have : (1 : ENNReal) = 0 := by
    simpa [hUnivOne] using hUnivZero
  exact one_ne_zero this

end FiniteDependence.Coloring
