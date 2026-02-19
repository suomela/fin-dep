import FiniteDependence.MIS.K5Bridge.Step2SparsePolys
import FiniteDependence.MIS.K5Elim

namespace FiniteDependence.MIS

/-!
Combine the two compatibility constraints `f(p,t)=0` and `g(p,t)=0` to obtain the
quartic factorization `A(p) * B(p) = 0`.

This file is purely algebraic once `f`/`g` have been bridged to the MIS model.
-/

namespace K5Bridge

open MeasureTheory Set
open scoped ProbabilityTheory

namespace Model

open FiniteDependence.MIS.Model

noncomputable section

namespace StepSolve

private lemma bezout_d_num (p : ℝ) :
    (19000 * p ^ 3 + 52550 * p ^ 2 + 64830 * p - 33275) * K5Elim.d (K := ℝ) p +
        (-1520 * p - 2076) * K5Elim.num (K := ℝ) p = (59 : ℝ) := by
  simp [K5Elim.d, K5Elim.num]
  ring

theorem d_ne_zero_prob (μ : Measure FiniteDependence.MIS.State) [IsProbabilityMeasure μ]
    (hstat : Stationary μ) (hdep : KDependent 5 μ) :
    K5Elim.d (K := ℝ)
        (FiniteDependence.MIS.Model.prob μ (cylStr (a := (0 : ℤ)) "1")) ≠ 0 := by
  classical
  set p : ℝ := FiniteDependence.MIS.Model.prob μ (cylStr (a := (0 : ℤ)) "1")
  set t : ℝ := FiniteDependence.MIS.Model.prob μ (cylStr (a := (0 : ℤ)) "1010101")

  have hg : K5Elim.g (K := ℝ) p t = 0 := by
    simpa [p, t, Step3.pVal, Step3.tVal] using (Step2Sparse.g_eq_zero_prob (μ := μ) hstat hdep)

  intro hd0
  have hnum0 : K5Elim.num (K := ℝ) p = 0 := by
    -- From `g = (15*d)*t - num`, if `d=0` then `num=0`.
    have hsub : ((15 : ℝ) * K5Elim.d (K := ℝ) p) * t - K5Elim.num (K := ℝ) p = 0 := by
      simpa [K5Elim.g_eq (p := p) (t := t)] using hg
    have : -(K5Elim.num (K := ℝ) p) = 0 := by
      simpa [hd0] using hsub
    exact neg_eq_zero.mp this

  have hBez := bezout_d_num p
  have : (59 : ℝ) = 0 := by
    -- Substitute `d p = 0` and `num p = 0` into the Bézout identity.
    simpa [hd0, hnum0] using hBez.symm
  norm_num at this

theorem AB_eq_zero_prob (μ : Measure FiniteDependence.MIS.State) [IsProbabilityMeasure μ]
    (hstat : Stationary μ) (hdep : KDependent 5 μ) :
    K5Elim.A (K := ℝ)
        (FiniteDependence.MIS.Model.prob μ (cylStr (a := (0 : ℤ)) "1")) *
      K5Elim.B (K := ℝ)
        (FiniteDependence.MIS.Model.prob μ (cylStr (a := (0 : ℤ)) "1")) = 0 := by
  classical
  set p : ℝ := FiniteDependence.MIS.Model.prob μ (cylStr (a := (0 : ℤ)) "1")
  set t : ℝ := FiniteDependence.MIS.Model.prob μ (cylStr (a := (0 : ℤ)) "1010101")

  have hf : K5Elim.f (K := ℝ) p t = 0 := by
    simpa [p, t, Step3.pVal, Step3.tVal] using (Step2Sparse.f_eq_zero_prob (μ := μ) hstat hdep)
  have hg : K5Elim.g (K := ℝ) p t = 0 := by
    simpa [p, t, Step3.pVal, Step3.tVal] using (Step2Sparse.g_eq_zero_prob (μ := μ) hstat hdep)
  have hd : K5Elim.d (K := ℝ) p ≠ 0 := by
    simpa [p] using (d_ne_zero_prob (μ := μ) hstat hdep)

  simpa [p, t] using (K5Elim.AB_eq_zero_of_fg (p := p) (t := t) hf hg hd)

theorem A_or_B_prob (μ : Measure FiniteDependence.MIS.State) [IsProbabilityMeasure μ]
    (hstat : Stationary μ) (hdep : KDependent 5 μ) :
    K5Elim.A (K := ℝ)
        (FiniteDependence.MIS.Model.prob μ (cylStr (a := (0 : ℤ)) "1")) = 0 ∨
      K5Elim.B (K := ℝ)
        (FiniteDependence.MIS.Model.prob μ (cylStr (a := (0 : ℤ)) "1")) = 0 := by
  exact mul_eq_zero.mp (AB_eq_zero_prob (μ := μ) hstat hdep)

theorem t_eq_tA_prob_of_A (μ : Measure FiniteDependence.MIS.State) [IsProbabilityMeasure μ]
    (hstat : Stationary μ) (hdep : KDependent 5 μ)
    (hA : K5Elim.A (K := ℝ) (Step3.pVal μ) = 0) :
    Step3.tVal μ = K5Elim.tA (K := ℝ) (Step3.pVal μ) := by
  have hg : K5Elim.g (K := ℝ) (Step3.pVal μ) (Step3.tVal μ) = 0 := by
    exact Step2Sparse.g_eq_zero_prob (μ := μ) hstat hdep
  have hd : K5Elim.d (K := ℝ) (Step3.pVal μ) ≠ 0 := by
    simpa [Step3.pVal] using (d_ne_zero_prob (μ := μ) hstat hdep)
  exact K5Elim.t_eq_tA_of_gA (K := ℝ) (p := Step3.pVal μ) (t := Step3.tVal μ) hg hA hd

theorem t_eq_tB_prob_of_B (μ : Measure FiniteDependence.MIS.State) [IsProbabilityMeasure μ]
    (hstat : Stationary μ) (hdep : KDependent 5 μ)
    (hB : K5Elim.B (K := ℝ) (Step3.pVal μ) = 0) :
    Step3.tVal μ = K5Elim.tB (K := ℝ) (Step3.pVal μ) := by
  have hg : K5Elim.g (K := ℝ) (Step3.pVal μ) (Step3.tVal μ) = 0 := by
    exact Step2Sparse.g_eq_zero_prob (μ := μ) hstat hdep
  have hd : K5Elim.d (K := ℝ) (Step3.pVal μ) ≠ 0 := by
    simpa [Step3.pVal] using (d_ne_zero_prob (μ := μ) hstat hdep)
  exact K5Elim.t_eq_tB_of_gB (K := ℝ) (p := Step3.pVal μ) (t := Step3.tVal μ) hg hB hd

end StepSolve

end

end Model

end K5Bridge

end FiniteDependence.MIS
