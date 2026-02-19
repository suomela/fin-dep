import FiniteDependence.MIS.K5Bridge.NoK5

namespace FiniteDependence.MIS

namespace K5Bridge

open MeasureTheory
open scoped ProbabilityTheory

/-- Public `k=5` contradiction exported from the bridge pipeline. -/
theorem no_stationary_fiveDependent (μ : Measure FiniteDependence.MIS.State) [IsProbabilityMeasure μ]
    (hstat : FiniteDependence.MIS.Model.Stationary μ) (hdep : FiniteDependence.MIS.Model.KDependent 5 μ) :
    False := by
  exact Model.NoK5.no_k5 (μ := μ) hstat hdep

/-- Public nonexistence form of the `k=5` contradiction. -/
theorem no_stationary_fiveDependent_exists :
    ¬ ∃ μ : Measure FiniteDependence.MIS.State,
        (IsProbabilityMeasure μ) ∧ FiniteDependence.MIS.Model.Stationary μ ∧
          FiniteDependence.MIS.Model.KDependent 5 μ := by
  exact Model.NoK5.no_k5_exists

end K5Bridge

end FiniteDependence.MIS
