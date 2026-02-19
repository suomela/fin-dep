import FiniteDependence.MIS.K2Model
import FiniteDependence.MIS.K3Model

namespace FiniteDependence.MIS

open MeasureTheory
open scoped ProbabilityTheory

/-!
# Model-level impossibility theorems

This module exposes contradictions proved directly from the State probability
model (`Measure State`), independent of the `k=5` bridge pipeline internals.
-/

theorem no_stationary_twoDependent_MIS (μ : Measure State) [IsProbabilityMeasure μ]
    (hstat : Model.Stationary μ) (hdep : Model.KDependent 2 μ) : False := by
  exact Model.no_stationary_kDependent_le2 (μ := μ) (hstat := hstat) (k := 2) (hk := by decide)
    (hdep := hdep)

theorem no_stationary_threeDependent_MIS (μ : Measure State) [IsProbabilityMeasure μ]
    (hstat : Model.Stationary μ) (hdep : Model.KDependent 3 μ) : False := by
  exact Model.no_stationary_threeDependent (μ := μ) hstat hdep

end FiniteDependence.MIS
