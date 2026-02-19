import FiniteDependence.Coloring.DependenceFour
import FiniteDependence.Coloring.DependenceThree
import FiniteDependence.Coloring.DependenceEquivalence

/-!
# Finitely dependent colorings of `ℤ`

This file contains Lean statements formalizing Theorem 1 of
Holroyd–Liggett, *Finitely dependent coloring* (arXiv:1403.2448v4):

* there exists a stationary 1-dependent 4-coloring of `ℤ`;
* there exists a stationary 2-dependent 3-coloring of `ℤ`.

This file is a thin wrapper bundling the two existence statements; the explicit constructions
(`Word.μ4`, `Word.μ3`) and proofs live in the imported `Dependence*` / `Properties*` modules. The
finite-dimensional cylinder weights `Word.P4` / `Word.P3` are in
`FiniteDependence.Coloring/Distributions.lean`.
-/

open scoped BigOperators

namespace FiniteDependence.Coloring

open MeasureTheory ProbabilityTheory

/-! ## Existence statements (Theorem 1) -/

/-- There exists a stationary 1-dependent 4-coloring of `ℤ`. -/
theorem exists_stationary_oneDependent_fourColoring :
    ∃ μ : ProbabilityMeasure (ℤ → Fin 4),
      IsStationary μ ∧
      IsKDependent μ 1 ∧
      (μ : Measure (ℤ → Fin 4)) {x | IsColoring x} = 1 := by
  classical
  exact ⟨Word.μ4, Word.μ4_isStationary, Word.μ4_isKDependent, Word.μ4_isColoring_ae⟩

/-- There exists a stationary 2-dependent 3-coloring of `ℤ`. -/
theorem exists_stationary_twoDependent_threeColoring :
    ∃ μ : ProbabilityMeasure (ℤ → Fin 3),
      IsStationary μ ∧
      IsKDependent μ 2 ∧
      (μ : Measure (ℤ → Fin 3)) {x | IsColoring x} = 1 := by
  classical
  exact ⟨Word.μ3, Word.μ3_isStationary, Word.μ3_isKDependent, Word.μ3_isColoring_ae⟩

/-! ## Existence statements (noncontiguous dependence) -/

/-- There exists a stationary 1-dependent 4-coloring of `ℤ` (noncontiguous definition). -/
theorem exists_stationary_oneDependent_fourColoring_noncontig :
    ∃ μ : ProbabilityMeasure (ℤ → Fin 4),
      IsStationary μ ∧
      IsKDependentNoncontig μ 1 ∧
      (μ : Measure (ℤ → Fin 4)) {x | IsColoring x} = 1 := by
  classical
  refine ⟨Word.μ4, Word.μ4_isStationary, ?_, Word.μ4_isColoring_ae⟩
  exact DependenceEquivalence.isKDependentNoncontig_of_isKDependent (q := 4) Word.μ4_isKDependent

/-- There exists a stationary 2-dependent 3-coloring of `ℤ` (noncontiguous definition). -/
theorem exists_stationary_twoDependent_threeColoring_noncontig :
    ∃ μ : ProbabilityMeasure (ℤ → Fin 3),
      IsStationary μ ∧
      IsKDependentNoncontig μ 2 ∧
      (μ : Measure (ℤ → Fin 3)) {x | IsColoring x} = 1 := by
  classical
  refine ⟨Word.μ3, Word.μ3_isStationary, ?_, Word.μ3_isColoring_ae⟩
  exact DependenceEquivalence.isKDependentNoncontig_of_isKDependent (q := 3) Word.μ3_isKDependent

end FiniteDependence.Coloring
