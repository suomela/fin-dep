import FiniteDependence.Coloring.ColoringProcess
import FiniteDependence.Coloring.ProjectiveThree
import Mathlib.MeasureTheory.Constructions.Projective

/-!
# The `q = 3` two-sided process on `ℤ`

This file records basic properties of the measure `Word.μ3` constructed in
`FiniteDependence.Coloring/ProjectiveThree.lean`.

The main technical tool is that `μ3Measure` is a projective limit of the finite-dimensional
measures `P3Family`.
-/

open scoped BigOperators

namespace FiniteDependence.Coloring

namespace Word

open MeasureTheory Set

lemma μ3Measure_eq_μ3Content {s : Set (ℤ → Fin 3)}
    (hs : s ∈ measurableCylinders (fun _ : ℤ => Fin 3)) :
    μ3Measure s = μ3Content s := by
  classical
  simp [μ3Measure, MeasureTheory.AddContent.measure_eq (m := μ3Content)
    (hC := MeasureTheory.isSetSemiring_measurableCylinders (α := fun _ : ℤ => Fin 3)
      (mα := fun _ : ℤ => inferInstance))
    (hC_gen := μ3Measure_generateFrom) (m_sigma_subadd := μ3Content_isSigmaSubadditive), hs]

lemma μ3Measure_cylinder (I : Finset ℤ) (S : Set (I → Fin 3)) (hS : MeasurableSet S) :
    μ3Measure (cylinder I S : Set (ℤ → Fin 3)) = P3Family I S := by
  have hs : (cylinder I S : Set (ℤ → Fin 3)) ∈ measurableCylinders (fun _ : ℤ => Fin 3) := by
    exact (mem_measurableCylinders _).2 ⟨I, S, hS, rfl⟩
  -- Reduce to the content, then evaluate the content on cylinders.
  rw [μ3Measure_eq_μ3Content (s := cylinder I S) hs]
  simpa [μ3Content] using
    (projectiveFamilyContent_cylinder (hP := P3Family_projective) (I := I) (S := S) hS)

lemma μ3_isProjectiveLimit :
    MeasureTheory.IsProjectiveLimit μ3Measure (fun I : Finset ℤ => P3Family I) := by
  classical
  intro I
  -- It suffices to check equality on singletons since the codomain is finite.
  refine Measure.ext_of_singleton (α := (I → Fin 3)) ?_
  intro f
  have hmeas : MeasurableSet ({f} : Set (I → Fin 3)) := measurableSet_singleton f
  -- Evaluate both measures on singletons via the cylinder formula.
  have :
      (μ3Measure.map I.restrict) {f} = P3Family I {f} := by
    have hmeas_restrict : Measurable (I.restrict : (ℤ → Fin 3) → I → Fin 3) :=
      measurable_pi_lambda _ (fun _ => measurable_pi_apply _)
    rw [Measure.map_apply hmeas_restrict hmeas]
    -- `I.restrict ⁻¹' {f}` is the cylinder determined by `f`.
    simpa [cylinder] using μ3Measure_cylinder (I := I) (S := ({f} : Set (I → Fin 3))) hmeas
  simpa using this

end Word

end FiniteDependence.Coloring

