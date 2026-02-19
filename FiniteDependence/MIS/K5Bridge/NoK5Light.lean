import FiniteDependence.MIS.K5Bridge.ABForced
import FiniteDependence.MIS.K5Bridge.Step4SparseQ

namespace FiniteDependence.MIS

namespace K5Bridge

open MeasureTheory Set
open scoped ProbabilityTheory

namespace Model

open FiniteDependence.MIS.Model

noncomputable section

namespace NoK5Light

def P12 (p : ℝ) : ℝ :=
  500 * p ^ 12 - 306000 * p ^ 11 + 976500 * p ^ 10 + 6273000 * p ^ 9 -
    11736300 * p ^ 8 - 1616400 * p ^ 7 + 16300800 * p ^ 6 - 13617000 * p ^ 5 +
    4003260 * p ^ 4 + 377640 * p ^ 3 - 541710 * p ^ 2 + 129690 * p - 10579

private theorem q_subst_num_identity (p : ℝ)
    (hd : K5Elim.d (K := ℝ) p ≠ 0) :
    (3375 : ℝ) * (K5Elim.d (K := ℝ) p) ^ 3 *
        Step4Sparse.qCompat p
          (K5Elim.num (K := ℝ) p / ((15 : ℝ) * K5Elim.d (K := ℝ) p)) =
      P12 p := by
  have h15 : (15 : ℝ) ≠ 0 := by norm_num
  have hden : ((15 : ℝ) * K5Elim.d (K := ℝ) p) ≠ 0 := mul_ne_zero h15 hd
  simp [Step4Sparse.qCompat, P12]
  field_simp [hden]
  simp [K5Elim.d, K5Elim.num]
  ring_nf

theorem P12_eq_zero_prob (μ : Measure FiniteDependence.MIS.State) [IsProbabilityMeasure μ]
    (hstat : Stationary μ) (hdep : KDependent 5 μ) :
    P12 (Step3.pVal μ) = 0 := by
  set p : ℝ := Step3.pVal μ
  set t : ℝ := Step3.tVal μ
  have hg : K5Elim.g (K := ℝ) p t = 0 := by
    simpa [p, t, Step3.pVal, Step3.tVal] using
      (Step2Sparse.g_eq_zero_prob (μ := μ) hstat hdep)
  have hq : Step4Sparse.qCompat p t = 0 := by
    simpa [p, t, Step3.pVal, Step3.tVal] using
      (Step4Sparse.qCompat_eq_zero_prob (μ := μ) hstat hdep)
  have hd : K5Elim.d (K := ℝ) p ≠ 0 := by
    simpa [p, Step3.pVal] using (StepSolve.d_ne_zero_prob (μ := μ) hstat hdep)
  have ht :
      t = K5Elim.num (K := ℝ) p / ((15 : ℝ) * K5Elim.d (K := ℝ) p) :=
    K5Elim.solve_t (K := ℝ) (p := p) (t := t) hg hd
  have hqSub :
      Step4Sparse.qCompat p
          (K5Elim.num (K := ℝ) p / ((15 : ℝ) * K5Elim.d (K := ℝ) p)) = 0 := by
    simpa [ht] using hq
  have hmul :
      (3375 : ℝ) * (K5Elim.d (K := ℝ) p) ^ 3 *
          Step4Sparse.qCompat p
            (K5Elim.num (K := ℝ) p / ((15 : ℝ) * K5Elim.d (K := ℝ) p)) = 0 := by
    simp [hqSub]
  have hId := q_subst_num_identity (p := p) hd
  have hP12 : P12 p = 0 := by
    linarith [hId, hmul]
  simpa [p, Step3.pVal] using hP12

private def UA12 (p : ℝ) : ℝ :=
  -161510176657484000 * p ^ 11 + 98774730167678481000 * p ^ 10 -
    272926536226178435600 * p ^ 9 - 2143747421380040960300 * p ^ 8 +
    2868608301844661706500 * p ^ 7 + 1756500185476286811000 * p ^ 6 -
    4509671956946079071560 * p ^ 5 + 2458046350142022827600 * p ^ 4 -
    235426288967646768500 * p ^ 3 - 223292221096594100220 * p ^ 2 +
    78900052934568643396 * p - 7941380392203123260

private def VA12 (p : ℝ) : ℝ :=
  1615101766574840 * p ^ 3 - 113977245959796370 * p ^ 2 +
    99544866322350186 * p - 21769546400793991

private theorem bezoutA_P12 (p : ℝ) :
    UA12 p * K5Elim.A (K := ℝ) p + VA12 p * P12 p = 109056249 := by
  simp [UA12, VA12, K5Elim.A, P12]
  ring_nf

private def UB12 (p : ℝ) : ℝ :=
  -4469172742000 * p ^ 11 + 2733222394923000 * p ^ 10 -
    7559381990545600 * p ^ 9 - 59303148713585300 * p ^ 8 +
    79541031666403900 * p ^ 7 + 48465113647180500 * p ^ 6 -
    124975192907326460 * p ^ 5 + 68265531277202900 * p ^ 4 -
    6587522158768960 * p ^ 3 - 6192750735073380 * p ^ 2 +
    2193548403290516 * p - 221103066519740

private def VB12 (p : ℝ) : ℝ :=
  44691727420 * p ^ 3 - 25578495610 * p ^ 2 - 55630837314 * p + 20900185889

private theorem bezoutB_P12 (p : ℝ) :
    UB12 p * K5Elim.B (K := ℝ) p + VB12 p * P12 p = 9 := by
  simp [UB12, VB12, K5Elim.B, P12]
  ring_nf

private theorem no_A_and_P12 (p : ℝ) (hA : K5Elim.A (K := ℝ) p = 0) (hP12 : P12 p = 0) : False := by
  have hBez := bezoutA_P12 (p := p)
  have : (109056249 : ℝ) = 0 := by
    simpa [hA, hP12] using hBez
  norm_num at this

private theorem no_B_and_P12 (p : ℝ) (hB : K5Elim.B (K := ℝ) p = 0) (hP12 : P12 p = 0) : False := by
  have hBez := bezoutB_P12 (p := p)
  have : (9 : ℝ) = 0 := by
    simpa [hB, hP12] using hBez
  norm_num at this

theorem no_k5 (μ : Measure FiniteDependence.MIS.State) [IsProbabilityMeasure μ]
    (hstat : Stationary μ) (hdep : KDependent 5 μ) : False := by
  have hAB :
      K5Elim.A (K := ℝ) (Step3.pVal μ) * K5Elim.B (K := ℝ) (Step3.pVal μ) = 0 :=
    StepSolve.AB_eq_zero_prob (μ := μ) hstat hdep
  have hP12 : P12 (Step3.pVal μ) = 0 := P12_eq_zero_prob (μ := μ) hstat hdep
  rcases mul_eq_zero.mp hAB with hA | hB
  · exact no_A_and_P12 (p := Step3.pVal μ) hA hP12
  · exact no_B_and_P12 (p := Step3.pVal μ) hB hP12

end NoK5Light

end

end Model

end K5Bridge

end FiniteDependence.MIS
