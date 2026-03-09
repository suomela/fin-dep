import FiniteDependence.MIS.K5Bridge.Length25Row2936
import FiniteDependence.MIS.K5Bridge.Length25Row5988
import FiniteDependence.MIS.K5Bridge.Length25Row9880
import FiniteDependence.MIS.K5Bridge.Length25Row2736

namespace FiniteDependence.MIS

namespace K5Bridge

open MeasureTheory Set
open scoped ProbabilityTheory

namespace Model

open FiniteDependence.MIS.Model

noncomputable section

theorem rhs_combination_eq_zero (μ : Measure FiniteDependence.MIS.State) [IsProbabilityMeasure μ]
    (hstat : Stationary μ) (hdep : KDependent 5 μ) :
    (FiniteDependence.MIS.Model.prob μ (cylStr (a := 0) "0") *
          FiniteDependence.MIS.Model.prob μ (cylStr (a := 0) suf19)) +
        (FiniteDependence.MIS.Model.prob μ (cylStr (a := 0) mid10)) ^ 2 -
        FiniteDependence.MIS.Model.prob μ (cylStr (a := 0) suf24) -
        (FiniteDependence.MIS.Model.prob μ (cylStr (a := 0) "00100") *
          FiniteDependence.MIS.Model.prob μ (cylStr (a := 0) suf15)) = 0 := by
  set xA : ℝ := FiniteDependence.MIS.Model.prob μ (cylStr (a := 0) wA)
  set xB : ℝ := FiniteDependence.MIS.Model.prob μ (cylStr (a := 0) wB)
  set xC : ℝ := FiniteDependence.MIS.Model.prob μ (cylStr (a := 0) wC)

  have h2936 :
      xA + xB =
        FiniteDependence.MIS.Model.prob μ (cylStr (a := 0) "0") *
          FiniteDependence.MIS.Model.prob μ (cylStr (a := 0) suf19) := by
    simpa [xA, xB] using prob_row2936 (μ := μ) hstat hdep
  have h9880 :
      xC = (FiniteDependence.MIS.Model.prob μ (cylStr (a := 0) mid10)) ^ 2 := by
    simpa [xC] using prob_row9880 (μ := μ) hstat hdep
  have h2736 :
      xB = FiniteDependence.MIS.Model.prob μ (cylStr (a := 0) suf24) := by
    simpa [xB] using prob_row2736 (μ := μ) hstat
  have h5988 :
      xA + xC =
        FiniteDependence.MIS.Model.prob μ (cylStr (a := 0) "00100") *
          FiniteDependence.MIS.Model.prob μ (cylStr (a := 0) suf15) := by
    simpa [xA, xC] using prob_row5988 (μ := μ) hstat hdep

  have hcancel : (xA + xB) + xC - xB - (xA + xC) = (0 : ℝ) := by ring
  have h1 :
      (FiniteDependence.MIS.Model.prob μ (cylStr (a := 0) "0") *
            FiniteDependence.MIS.Model.prob μ (cylStr (a := 0) suf19)) +
          xC - xB -
            (FiniteDependence.MIS.Model.prob μ (cylStr (a := 0) "00100") *
              FiniteDependence.MIS.Model.prob μ (cylStr (a := 0) suf15)) = (0 : ℝ) := by
    simpa [h2936, h5988] using hcancel
  have h2 :
      (FiniteDependence.MIS.Model.prob μ (cylStr (a := 0) "0") *
            FiniteDependence.MIS.Model.prob μ (cylStr (a := 0) suf19)) +
          (FiniteDependence.MIS.Model.prob μ (cylStr (a := 0) mid10)) ^ 2 -
            FiniteDependence.MIS.Model.prob μ (cylStr (a := 0) suf24) -
            (FiniteDependence.MIS.Model.prob μ (cylStr (a := 0) "00100") *
              FiniteDependence.MIS.Model.prob μ (cylStr (a := 0) suf15)) = (0 : ℝ) := by
    simpa [h9880, h2736, sub_eq_add_neg, add_assoc, add_left_comm, add_comm] using h1
  simpa [sub_eq_add_neg, add_assoc, add_left_comm, add_comm] using h2

end

end Model

end K5Bridge

end FiniteDependence.MIS
