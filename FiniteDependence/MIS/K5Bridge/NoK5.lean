import FiniteDependence.MIS.K5Bridge.NoK5Light

namespace FiniteDependence.MIS

/-!
## k=5 impossibility (lightweight sparse path)
-/

namespace K5Bridge

open MeasureTheory Set
open scoped ProbabilityTheory

namespace Model

open FiniteDependence.MIS.Model

noncomputable section

namespace NoK5

theorem no_k5 (μ : Measure FiniteDependence.MIS.State) [IsProbabilityMeasure μ]
    (hstat : Stationary μ) (hdep : KDependent 5 μ) : False := by
  exact NoK5Light.no_k5 (μ := μ) hstat hdep

theorem no_k5_exists :
    ¬ ∃ μ : Measure FiniteDependence.MIS.State,
        (IsProbabilityMeasure μ) ∧ Stationary μ ∧ KDependent 5 μ := by
  intro h
  rcases h with ⟨μ, hprob, hstat, hdep⟩
  classical
  -- Make the `IsProbabilityMeasure` instance available.
  letI : IsProbabilityMeasure μ := hprob
  exact no_k5 (μ := μ) hstat hdep

end NoK5

end

end Model

end K5Bridge

end FiniteDependence.MIS
