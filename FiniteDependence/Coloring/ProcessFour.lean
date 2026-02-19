import FiniteDependence.Coloring.ColoringProcess
import FiniteDependence.Coloring.ProjectiveFour
import Mathlib.MeasureTheory.Constructions.Projective

/-!
# The `q = 4` two-sided process on `ℤ`

This file records basic properties of the measure `Word.μ4` constructed in
`FiniteDependence.Coloring/ProjectiveFour.lean`.

The main technical tool is that `μ4Measure` is a projective limit of the finite-dimensional
measures `P4Family`.
-/

open scoped BigOperators

namespace FiniteDependence.Coloring

namespace Word

open MeasureTheory Set

lemma μ4Measure_eq_μ4Content {s : Set (ℤ → Fin 4)}
    (hs : s ∈ measurableCylinders (fun _ : ℤ => Fin 4)) :
    μ4Measure s = μ4Content s := by
  classical
  simp [μ4Measure, MeasureTheory.AddContent.measure_eq (m := μ4Content)
    (hC := MeasureTheory.isSetSemiring_measurableCylinders (α := fun _ : ℤ => Fin 4)
      (mα := fun _ : ℤ => inferInstance))
    (hC_gen := μ4Measure_generateFrom) (m_sigma_subadd := μ4Content_isSigmaSubadditive), hs]

lemma μ4Measure_cylinder (I : Finset ℤ) (S : Set (I → Fin 4)) (hS : MeasurableSet S) :
    μ4Measure (cylinder I S : Set (ℤ → Fin 4)) = P4Family I S := by
  have hs : (cylinder I S : Set (ℤ → Fin 4)) ∈ measurableCylinders (fun _ : ℤ => Fin 4) := by
    exact (mem_measurableCylinders _).2 ⟨I, S, hS, rfl⟩
  -- Reduce to the content, then evaluate the content on cylinders.
  rw [μ4Measure_eq_μ4Content (s := cylinder I S) hs]
  simpa [μ4Content] using
    (projectiveFamilyContent_cylinder (hP := P4Family_projective) (I := I) (S := S) hS)

lemma μ4_isProjectiveLimit :
    MeasureTheory.IsProjectiveLimit μ4Measure (fun I : Finset ℤ => P4Family I) := by
  classical
  intro I
  -- It suffices to check equality on singletons since the codomain is finite.
  refine Measure.ext_of_singleton (α := (I → Fin 4)) ?_
  intro f
  have hmeas : MeasurableSet ({f} : Set (I → Fin 4)) := measurableSet_singleton f
  -- Evaluate both measures on singletons via the cylinder formula.
  have :
      (μ4Measure.map I.restrict) {f} = P4Family I {f} := by
    have hmeas_restrict : Measurable (I.restrict : (ℤ → Fin 4) → I → Fin 4) :=
      measurable_pi_lambda _ (fun _ => measurable_pi_apply _)
    rw [Measure.map_apply hmeas_restrict hmeas]
    -- `I.restrict ⁻¹' {f}` is the cylinder determined by `f`.
    simpa [cylinder] using μ4Measure_cylinder (I := I) (S := ({f} : Set (I → Fin 4))) hmeas
  simpa using this

end Word

end FiniteDependence.Coloring
