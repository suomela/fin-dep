import FiniteDependence.MIS.K5Bridge.Public

namespace FiniteDependence.MIS

open MeasureTheory
open scoped ProbabilityTheory

/-!
# Bridge-level `k=5` impossibility theorems

This module exposes the public consequences of the certificate/bridge pipeline
without requiring downstream files to depend on `K5Bridge` internals.
-/

theorem no_stationary_fiveDependent_MIS (μ : Measure State) [IsProbabilityMeasure μ]
    (hstat : Model.Stationary μ) (hdep : Model.KDependent 5 μ) : False := by
  exact K5Bridge.no_stationary_fiveDependent (μ := μ) hstat hdep

theorem no_stationary_fiveDependent_MIS_exists :
    ¬ ∃ μ : Measure State, (IsProbabilityMeasure μ) ∧ Model.Stationary μ ∧ Model.KDependent 5 μ := by
  exact K5Bridge.no_stationary_fiveDependent_exists

end FiniteDependence.MIS
