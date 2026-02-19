import FiniteDependence.MIS.K5Bridge.Words
import FiniteDependence.MIS.K5Data.Defs
import FiniteDependence.MIS.Prob

namespace FiniteDependence.MIS

/-!
The `k=5` bridge works with arrays of values indexed by `K5Data.allowedWords L` (strings).

This file defines the corresponding arrays coming from an actual State probability measure.
-/

open MeasureTheory Set

open scoped BigOperators ProbabilityTheory

namespace K5Bridge

open K5Data

namespace Model

noncomputable section

/-- Cylinder set for a binary string at position `a`. -/
def cylStr (a : ℤ) (s : String) : Set FiniteDependence.MIS.State :=
  FiniteDependence.MIS.Model.cyl a (K5Bridge.wordOfString s)

/-- Stationarity gives shift-invariance of `cylStr` probabilities. -/
theorem Stationary.prob_cylStr_succ {μ : Measure FiniteDependence.MIS.State} [IsProbabilityMeasure μ]
    (hμ : FiniteDependence.MIS.Model.Stationary μ) (a : ℤ) (s : String) :
    FiniteDependence.MIS.Model.prob μ (cylStr (a := a + 1) s) =
      FiniteDependence.MIS.Model.prob μ (cylStr (a := a) s) := by
  -- Reduce to the `Fin n → Bool` cylinder lemma.
  simpa [cylStr] using
    (FiniteDependence.MIS.Model.Stationary.prob_cyl_succ (μ := μ) hμ (a := a) (w := K5Bridge.wordOfString s))

/-- The length-`L` distribution induced by `μ`, indexed by `allowedWords L`. -/
def dist (μ : Measure FiniteDependence.MIS.State) [IsProbabilityMeasure μ] (L : Nat) : Array ℝ :=
  (K5Data.allowedWords L).map (fun s => FiniteDependence.MIS.Model.prob μ (cylStr (a := 0) s))

end

end Model

end K5Bridge

end FiniteDependence.MIS
