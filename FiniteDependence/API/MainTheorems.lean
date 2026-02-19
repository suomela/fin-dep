import FiniteDependence.API.Definitions

import FiniteDependence.Coloring.DependenceEquivalence
import FiniteDependence.Coloring.Existence
import FiniteDependence.Coloring.GreedyThree
import FiniteDependence.Coloring.LowerBounds
import FiniteDependence.Coloring.MIS
import FiniteDependence.MIS.LowerBounds.K5.Bridge
import FiniteDependence.WeakTwo.Threshold

/-!
# Human-facing theorems

This file is the public theorem interface for the project.

It explicitly states the main formalized results:

- equivalence of contiguous and noncontiguous finite dependence;
- existence/non-existence for `4`-colorings (`1` vs `0`);
- existence/non-existence for `3`-colorings (`2` vs `1`);
- existence/non-existence for weak-2-colorings (`3` vs `2`);
- existence/non-existence for greedy proper `3`-colorings (`6` vs `5`);
- existence/non-existence for MIS (`6` vs `5`).

The proofs here are intentionally short wrappers around implementation theorems elsewhere.
-/

namespace FiniteDependence

open MeasureTheory ProbabilityTheory

/-- For `Fin q`-valued processes on `ℤ`, contiguous and noncontiguous `k`-dependence are equivalent. -/
theorem isKDependentCut_iff_isKDependentNoncontigConfig {q : ℕ}
    (μ : ProbabilityMeasure (ℤ → Fin q)) (k : ℕ) :
    IsKDependentCut μ k ↔ IsKDependentNoncontigConfig μ k := by
  simpa [IsKDependentCut, IsKDependentNoncontigConfig,
    FiniteDependence.Coloring.IsKDependent, FiniteDependence.Coloring.IsKDependentNoncontig] using
    (FiniteDependence.Coloring.DependenceEquivalence.isKDependent_iff_isKDependentNoncontig
      (q := q) (μ := μ) (k := k))

/-- A stationary `1`-dependent proper `4`-coloring law exists on `ℤ`. -/
theorem exists_stationary_oneDependent_fourColoring :
    ExistsStationaryKDependentColoring 4 1 := by
  simpa [ExistsStationaryKDependentColoring, IsStationaryKDependentColoring, IsKDependentCut,
    FiniteDependence.Coloring.IsStationary, FiniteDependence.Coloring.IsKDependent,
    FiniteDependence.Coloring.IsColoring] using
    (FiniteDependence.Coloring.exists_stationary_oneDependent_fourColoring)

/-- No stationary `0`-dependent proper `4`-coloring law exists on `ℤ`. -/
theorem not_exists_stationary_zeroDependent_fourColoring :
    ¬ ExistsStationaryKDependentColoring 4 0 := by
  simpa [ExistsStationaryKDependentColoring, IsStationaryKDependentColoring,
    IsKDependentCut, FiniteDependence.Coloring.IsStationary,
    FiniteDependence.Coloring.IsKDependent, FiniteDependence.Coloring.IsColoring] using
    (FiniteDependence.Coloring.not_exists_stationary_zeroDependent_fourColoring)

/-- A stationary `2`-dependent proper `3`-coloring law exists on `ℤ`. -/
theorem exists_stationary_twoDependent_threeColoring :
    ExistsStationaryKDependentColoring 3 2 := by
  simpa [ExistsStationaryKDependentColoring, IsStationaryKDependentColoring, IsKDependentCut,
    FiniteDependence.Coloring.IsStationary, FiniteDependence.Coloring.IsKDependent,
    FiniteDependence.Coloring.IsColoring] using
    (FiniteDependence.Coloring.exists_stationary_twoDependent_threeColoring)

/-- No stationary `1`-dependent proper `3`-coloring law exists on `ℤ`. -/
theorem not_exists_stationary_oneDependent_threeColoring :
    ¬ ExistsStationaryKDependentColoring 3 1 := by
  simpa [ExistsStationaryKDependentColoring, IsStationaryKDependentColoring] using
    (FiniteDependence.WeakTwo.not_exists_stationary_oneDependent_threeColoring)

/-- A stationary `3`-dependent weak-2-coloring law exists on `ℤ`. -/
theorem exists_stationary_threeDependent_weakTwoColoring :
    ExistsStationaryKDependentWeakTwoColoring 3 :=
  FiniteDependence.WeakTwo.exists_stationary_threeDependent_weakTwoColoring

/-- No stationary `2`-dependent weak-2-coloring law exists on `ℤ`. -/
theorem not_exists_stationary_twoDependent_weakTwoColoring :
    ¬ ExistsStationaryKDependentWeakTwoColoring 2 :=
  FiniteDependence.WeakTwo.not_exists_stationary_twoDependent_weakTwoColoring

/-- A stationary `6`-dependent greedy proper `3`-coloring law exists on `ℤ`. -/
theorem exists_stationary_sixDependent_greedyThreeColoring :
    ExistsStationaryKDependentGreedyThreeColoring 6 := by
  simpa [ExistsStationaryKDependentGreedyThreeColoring,
    IsStationaryKDependentGreedyThreeColoring] using
    (FiniteDependence.Coloring.exists_stationary_sixDependent_greedyThreeColoring)

/-- No stationary `5`-dependent greedy proper `3`-coloring law exists on `ℤ`. -/
theorem not_exists_stationary_fiveDependent_greedyThreeColoring :
    ¬ ExistsStationaryKDependentGreedyThreeColoring 5 := by
  simpa [ExistsStationaryKDependentGreedyThreeColoring,
    IsStationaryKDependentGreedyThreeColoring] using
    (FiniteDependence.Coloring.not_exists_stationary_fiveDependent_greedyThreeColoring)

/-- A stationary `6`-dependent MIS law exists on `ℤ`. -/
theorem exists_stationary_sixDependent_MIS : ExistsStationaryKDependentMIS 6 := by
  simpa [ExistsStationaryKDependentMIS, IsStationaryKDependentMIS, IsKDependentCut,
    FiniteDependence.Coloring.IsStationary, FiniteDependence.Coloring.IsKDependent,
    FiniteDependence.Coloring.IsMIS] using
    (FiniteDependence.Coloring.exists_stationary_sixDependent_MIS)

/-- No stationary `5`-dependent MIS law exists on `ℤ`. -/
theorem not_exists_stationary_fiveDependent_MIS :
    ¬ ExistsStationaryKDependentMIS 5 :=
  FiniteDependence.LowerBoundBridge.not_exists_stationary_fiveDependent_MIS

end FiniteDependence
