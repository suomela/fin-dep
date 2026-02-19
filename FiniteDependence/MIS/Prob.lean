import FiniteDependence.MIS.Model

namespace FiniteDependence.MIS

open MeasureTheory Set

open scoped ProbabilityTheory

namespace Model

noncomputable section

/-- Real-valued probability of an event under a (finite) measure, via `ENNReal.toReal`. -/
def prob (μ : Measure State) (s : Set State) : ℝ :=
  (μ s).toReal

theorem prob_univ (μ : Measure State) [IsProbabilityMeasure μ] : prob μ (univ : Set State) = 1 := by
  simp [prob]

theorem prob_empty (μ : Measure State) : prob μ (∅ : Set State) = 0 := by
  simp [prob]

theorem prob_union {μ : Measure State} [IsProbabilityMeasure μ] {s t : Set State}
    (hdisj : Disjoint s t) (ht : MeasurableSet t) :
    prob μ (s ∪ t) = prob μ s + prob μ t := by
  have h := measure_union (μ := μ) hdisj ht
  have h' := congrArg ENNReal.toReal h
  have hs_top : μ s ≠ (⊤ : ENNReal) := measure_ne_top μ s
  have ht_top : μ t ≠ (⊤ : ENNReal) := measure_ne_top μ t
  simpa [prob, ENNReal.toReal_add hs_top ht_top] using h'

theorem prob_union_cyl_of_ne {μ : Measure State} [IsProbabilityMeasure μ] (a : ℤ)
    {n : ℕ} {u v : Fin n → Bool} (huv : u ≠ v) :
    prob μ (cyl a u ∪ cyl a v) = prob μ (cyl a u) + prob μ (cyl a v) := by
  refine prob_union (μ := μ) ?_ ?_
  · exact disjoint_cyl_of_ne (a := a) huv
  · exact measurableSet_cyl a v

theorem Stationary.prob_cyl_succ {μ : Measure State} (hμ : Stationary μ) {n : ℕ} (a : ℤ)
    (w : Fin n → Bool) : prob μ (cyl (a + 1) w) = prob μ (cyl a w) := by
  -- Convert the `ENNReal` statement in `Model.lean` to reals.
  have h := Stationary.measure_cyl_succ (μ := μ) hμ (a := a) (w := w)
  -- `simp` knows `ENNReal.toReal_mul` but not needed here.
  simpa [prob] using congrArg ENNReal.toReal h

theorem Stationary.prob_cyl_add_nat {μ : Measure State} (hμ : Stationary μ) {n : ℕ} (a : ℤ)
    (s : ℕ) (w : Fin n → Bool) : prob μ (cyl (a + s) w) = prob μ (cyl a w) := by
  have h := Stationary.measure_cyl_add_nat (μ := μ) hμ (a := a) (s := s) (w := w)
  simpa [prob] using congrArg ENNReal.toReal h

theorem KDependent.prob_inter_cyl_eq_mul {μ : Measure State} {k m n : ℕ} {a b : ℤ}
    (hμ : KDependent k μ)
    (hsep :
      ∀ i : Fin m, ∀ j : Fin n,
        Int.natAbs ((a + Int.ofNat i.1) - (b + Int.ofNat j.1)) > k)
    (w : Fin m → Bool) (v : Fin n → Bool) :
    prob μ (cyl a w ∩ cyl b v) = prob μ (cyl a w) * prob μ (cyl b v) := by
  have h :=
    KDependent.measure_inter_cyl_eq_mul (μ := μ) (k := k) (m := m) (n := n) (a := a) (b := b) hμ hsep w v
  -- Convert to reals using `ENNReal.toReal_mul`.
  have := congrArg ENNReal.toReal h
  simpa [prob, ENNReal.toReal_mul] using this

end

end Model

end FiniteDependence.MIS
