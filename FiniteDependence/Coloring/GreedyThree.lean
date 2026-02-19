import FiniteDependence.API.Definitions
import FiniteDependence.Core.MeasurablePredicates
import FiniteDependence.Coloring.MeasureHelpers
import FiniteDependence.WeakTwo.Threshold
import FiniteDependence.MIS.LowerBounds.K5.Bridge

import Mathlib.MeasureTheory.Measure.Map
import Mathlib.MeasureTheory.MeasurableSpace.Prod
import Mathlib.Tactic

/-!
# Greedy proper 3-colorings on `ℤ`

This module adds the greedy 3-coloring threshold:

* existence of a stationary `6`-dependent greedy 3-coloring (via a local factor of weak-2);
* non-existence of a stationary `5`-dependent greedy 3-coloring (via reduction to MIS).
-/

namespace FiniteDependence.Coloring

open MeasureTheory ProbabilityTheory Set

/-! ## Local factor from weak-2 to greedy-3 -/

private def greedy3Factor4 : Fin 2 → Fin 2 → Fin 2 → Fin 2 → Fin 3
  | 0, 0, 1, 0 => 2
  | 0, 1, 1, 0 => 1
  | 1, 0, 0, 1 => 1
  | 1, 0, 1, 0 => 1
  | 1, 0, 1, 1 => 2
  | _, _, _, _ => 0

private def greedyThreeFromWeak (x : ℤ → Fin 2) : ℤ → Fin 3 :=
  fun i => greedy3Factor4 (x i) (x (i + 1)) (x (i + 2)) (x (i + 3))

private def greedy3Factor4Tuple (t : Fin 2 × Fin 2 × Fin 2 × Fin 2) : Fin 3 :=
  greedy3Factor4 t.1 t.2.1 t.2.2.1 t.2.2.2

private lemma measurable_greedy3Factor4Tuple : Measurable greedy3Factor4Tuple := by
  classical
  simpa [greedy3Factor4Tuple] using (Measurable.of_discrete : Measurable greedy3Factor4Tuple)

private lemma measurable_greedyThreeFromWeak_at {m : MeasurableSpace (ℤ → Fin 2)} (i : ℤ)
    (h0 : Measurable[m] fun x : ℤ → Fin 2 => x i)
    (h1 : Measurable[m] fun x : ℤ → Fin 2 => x (i + 1))
    (h2 : Measurable[m] fun x : ℤ → Fin 2 => x (i + 2))
    (h3 : Measurable[m] fun x : ℤ → Fin 2 => x (i + 3)) :
    Measurable[m] fun x : ℤ → Fin 2 => greedyThreeFromWeak x i := by
  have htuple : Measurable[m] fun x : ℤ → Fin 2 => (x i, x (i + 1), x (i + 2), x (i + 3)) :=
    h0.prodMk (h1.prodMk (h2.prodMk h3))
  simpa [greedyThreeFromWeak, greedy3Factor4Tuple] using measurable_greedy3Factor4Tuple.comp htuple

private lemma measurable_greedyThreeFromWeak : Measurable greedyThreeFromWeak := by
  classical
  refine measurable_pi_lambda _ (fun i => ?_)
  exact measurable_greedyThreeFromWeak_at (m := inferInstance) (i := i)
    (h0 := by simpa using (measurable_pi_apply (a := i)))
    (h1 := by simpa using (measurable_pi_apply (a := i + 1)))
    (h2 := by simpa using (measurable_pi_apply (a := i + 2)))
    (h3 := by simpa using (measurable_pi_apply (a := i + 3)))

private lemma greedyThreeFromWeak_shift (x : ℤ → Fin 2) :
    greedyThreeFromWeak (FiniteDependence.Coloring.shift (q := 2) x)
      = FiniteDependence.Coloring.shift (q := 3) (greedyThreeFromWeak x) := by
  ext i
  simp [greedyThreeFromWeak, FiniteDependence.Coloring.shift, FiniteDependence.shift,
    add_assoc, add_left_comm, add_comm]

private def goodTriple (a b c : Fin 2) : Prop :=
  ¬(a = 0 ∧ b = 0 ∧ c = 0) ∧ ¬(a = 1 ∧ b = 1 ∧ c = 1)

private instance decGoodTriple (a b c : Fin 2) : Decidable (goodTriple a b c) := by
  unfold goodTriple
  infer_instance

private lemma greedy3_proper_local :
    ∀ a b c d e : Fin 2,
      goodTriple a b c → goodTriple b c d → goodTriple c d e →
        greedy3Factor4 a b c d ≠ greedy3Factor4 b c d e := by
  decide

private lemma greedy3_color1_local :
    ∀ a b c d e f : Fin 2,
      goodTriple a b c → goodTriple b c d → goodTriple c d e → goodTriple d e f →
        greedy3Factor4 b c d e = 1 →
          greedy3Factor4 a b c d = 0 ∨ greedy3Factor4 c d e f = 0 := by
  decide

private lemma greedy3_color2_local :
    ∀ a b c d e f : Fin 2,
      goodTriple a b c → goodTriple b c d → goodTriple c d e → goodTriple d e f →
        greedy3Factor4 b c d e = 2 →
          (greedy3Factor4 a b c d = 0 ∨ greedy3Factor4 c d e f = 0) ∧
            (greedy3Factor4 a b c d = 1 ∨ greedy3Factor4 c d e f = 1) := by
  decide

private lemma goodTriple_of_isWeak (x : ℤ → Fin 2) (hx : IsWeakTwoColoring x) (i : ℤ) :
    goodTriple (x i) (x (i + 1)) (x (i + 2)) := by
  rcases hx with ⟨h000, h111⟩
  exact ⟨h000 i, h111 i⟩

private lemma greedyThreeFromWeak_isGreedy_of_isWeak (x : ℤ → Fin 2) (hx : IsWeakTwoColoring x) :
    IsGreedyThreeColoring (greedyThreeFromWeak x) := by
  refine ⟨?_, ?_, ?_⟩
  · intro i
    have hgt0 : goodTriple (x i) (x (i + 1)) (x (i + 2)) := goodTriple_of_isWeak x hx i
    have hgt1 : goodTriple (x (i + 1)) (x (i + 2)) (x (i + 3)) := by
      simpa [add_assoc] using (goodTriple_of_isWeak x hx (i + 1))
    have hgt2 : goodTriple (x (i + 2)) (x (i + 3)) (x (i + 4)) := by
      simpa [add_assoc] using (goodTriple_of_isWeak x hx (i + 2))
    simpa [greedyThreeFromWeak, add_assoc] using
      (greedy3_proper_local
        (a := x i) (b := x (i + 1)) (c := x (i + 2)) (d := x (i + 3)) (e := x (i + 4))
        hgt0 hgt1 hgt2)
  · intro i hi1
    have hgtm1 : goodTriple (x (i - 1)) (x i) (x (i + 1)) := by
      simpa [sub_eq_add_neg, add_assoc, add_left_comm, add_comm] using
        (goodTriple_of_isWeak x hx (i - 1))
    have hgt0 : goodTriple (x i) (x (i + 1)) (x (i + 2)) := goodTriple_of_isWeak x hx i
    have hgt1 : goodTriple (x (i + 1)) (x (i + 2)) (x (i + 3)) := by
      simpa [add_assoc] using (goodTriple_of_isWeak x hx (i + 1))
    have hgt2 : goodTriple (x (i + 2)) (x (i + 3)) (x (i + 4)) := by
      simpa [add_assoc] using (goodTriple_of_isWeak x hx (i + 2))
    have hloc := greedy3_color1_local
      (a := x (i - 1)) (b := x i) (c := x (i + 1)) (d := x (i + 2))
      (e := x (i + 3)) (f := x (i + 4)) hgtm1 hgt0 hgt1 hgt2
      (by simpa [greedyThreeFromWeak, add_assoc] using hi1)
    simpa [greedyThreeFromWeak, sub_eq_add_neg, add_assoc, add_left_comm, add_comm] using hloc
  · intro i hi2
    have hgtm1 : goodTriple (x (i - 1)) (x i) (x (i + 1)) := by
      simpa [sub_eq_add_neg, add_assoc, add_left_comm, add_comm] using
        (goodTriple_of_isWeak x hx (i - 1))
    have hgt0 : goodTriple (x i) (x (i + 1)) (x (i + 2)) := goodTriple_of_isWeak x hx i
    have hgt1 : goodTriple (x (i + 1)) (x (i + 2)) (x (i + 3)) := by
      simpa [add_assoc] using (goodTriple_of_isWeak x hx (i + 1))
    have hgt2 : goodTriple (x (i + 2)) (x (i + 3)) (x (i + 4)) := by
      simpa [add_assoc] using (goodTriple_of_isWeak x hx (i + 2))
    have hloc := greedy3_color2_local
      (a := x (i - 1)) (b := x i) (c := x (i + 1)) (d := x (i + 2))
      (e := x (i + 3)) (f := x (i + 4)) hgtm1 hgt0 hgt1 hgt2
      (by simpa [greedyThreeFromWeak, add_assoc] using hi2)
    simpa [greedyThreeFromWeak, sub_eq_add_neg, add_assoc, add_left_comm, add_comm] using hloc

/-! ## Dependence transfer helpers -/

private lemma comap_past_le_greedy3 (i : ℤ) :
    (FiniteDependence.Coloring.pastMeasurableSpace (q := 3) i).comap greedyThreeFromWeak
      ≤ FiniteDependence.Coloring.pastMeasurableSpace (q := 2) (i + 3) := by
  classical
  unfold FiniteDependence.Coloring.pastMeasurableSpace FiniteDependence.pastMeasurableSpace
  simp [MeasurableSpace.comap_iSup, MeasurableSpace.comap_comp]
  intro a ha
  have h0 : a < i + 3 := by linarith [ha]
  have h1 : a + 1 < i + 3 := by linarith [ha]
  have h2 : a + 2 < i + 3 := by linarith [ha]
  have h3 : a + 3 < i + 3 := by linarith [ha]
  have hm0 : Measurable[FiniteDependence.Coloring.pastMeasurableSpace (q := 2) (i + 3)]
      fun x : ℤ → Fin 2 => x a :=
    measurable_apply_past (q := 2) (i := i + 3) (j := a) h0
  have hm1 : Measurable[FiniteDependence.Coloring.pastMeasurableSpace (q := 2) (i + 3)]
      fun x : ℤ → Fin 2 => x (a + 1) :=
    measurable_apply_past (q := 2) (i := i + 3) (j := a + 1) h1
  have hm2 : Measurable[FiniteDependence.Coloring.pastMeasurableSpace (q := 2) (i + 3)]
      fun x : ℤ → Fin 2 => x (a + 2) :=
    measurable_apply_past (q := 2) (i := i + 3) (j := a + 2) h2
  have hm3 : Measurable[FiniteDependence.Coloring.pastMeasurableSpace (q := 2) (i + 3)]
      fun x : ℤ → Fin 2 => x (a + 3) :=
    measurable_apply_past (q := 2) (i := i + 3) (j := a + 3) h3
  have hmeas :
      Measurable[FiniteDependence.Coloring.pastMeasurableSpace (q := 2) (i + 3)]
        fun x : ℤ → Fin 2 => greedyThreeFromWeak x a :=
    measurable_greedyThreeFromWeak_at
      (m := FiniteDependence.Coloring.pastMeasurableSpace (q := 2) (i + 3)) (i := a)
      (h0 := hm0) (h1 := hm1) (h2 := hm2) (h3 := hm3)
  simpa [Function.comp] using hmeas.comap_le

private lemma comap_future_le_greedy3 (i : ℤ) :
    (FiniteDependence.Coloring.futureMeasurableSpace (q := 3) i 6).comap greedyThreeFromWeak
      ≤ FiniteDependence.Coloring.futureMeasurableSpace (q := 2) (i + 3) 3 := by
  classical
  unfold FiniteDependence.Coloring.futureMeasurableSpace FiniteDependence.futureMeasurableSpace
  simp [MeasurableSpace.comap_iSup, MeasurableSpace.comap_comp]
  intro a ha
  have h0 : i + 3 + 3 ≤ a := by linarith [ha]
  have h1 : i + 3 + 3 ≤ a + 1 := by linarith [ha]
  have h2 : i + 3 + 3 ≤ a + 2 := by linarith [ha]
  have h3 : i + 3 + 3 ≤ a + 3 := by linarith [ha]
  have hm0 : Measurable[FiniteDependence.Coloring.futureMeasurableSpace (q := 2) (i + 3) 3]
      fun x : ℤ → Fin 2 => x a :=
    measurable_apply_future (q := 2) (i := i + 3) (k := 3) (j := a) h0
  have hm1 : Measurable[FiniteDependence.Coloring.futureMeasurableSpace (q := 2) (i + 3) 3]
      fun x : ℤ → Fin 2 => x (a + 1) :=
    measurable_apply_future (q := 2) (i := i + 3) (k := 3) (j := a + 1) h1
  have hm2 : Measurable[FiniteDependence.Coloring.futureMeasurableSpace (q := 2) (i + 3) 3]
      fun x : ℤ → Fin 2 => x (a + 2) :=
    measurable_apply_future (q := 2) (i := i + 3) (k := 3) (j := a + 2) h2
  have hm3 : Measurable[FiniteDependence.Coloring.futureMeasurableSpace (q := 2) (i + 3) 3]
      fun x : ℤ → Fin 2 => x (a + 3) :=
    measurable_apply_future (q := 2) (i := i + 3) (k := 3) (j := a + 3) h3
  have hmeas :
      Measurable[FiniteDependence.Coloring.futureMeasurableSpace (q := 2) (i + 3) 3]
        fun x : ℤ → Fin 2 => greedyThreeFromWeak x a :=
    measurable_greedyThreeFromWeak_at
      (m := FiniteDependence.Coloring.futureMeasurableSpace (q := 2) (i + 3) 3) (i := a)
      (h0 := hm0) (h1 := hm1) (h2 := hm2) (h3 := hm3)
  simpa [Function.comp] using hmeas.comap_le

/-! ## Existence at dependence range 6 -/

/-- A stationary `6`-dependent greedy proper `3`-coloring law exists on `ℤ`. -/
theorem exists_stationary_sixDependent_greedyThreeColoring :
    ∃ μ : ProbabilityMeasure (ℤ → Fin 3),
      IsStationary μ ∧
      IsKDependentCut μ 6 ∧
      (μ : Measure (ℤ → Fin 3)) {x | IsGreedyThreeColoring x} = 1 := by
  rcases FiniteDependence.WeakTwo.exists_stationary_threeDependent_weakTwoColoring with
    ⟨μ2, hstat2, hdep3, hweak2⟩
  let μ3 : ProbabilityMeasure (ℤ → Fin 3) := μ2.map measurable_greedyThreeFromWeak.aemeasurable
  refine ⟨μ3, ?_, ?_, ?_⟩
  · have hcomm :
        (FiniteDependence.Coloring.shift (q := 3)) ∘ greedyThreeFromWeak
          = greedyThreeFromWeak ∘ (FiniteDependence.Coloring.shift (q := 2)) := by
      funext x
      simpa [Function.comp] using (greedyThreeFromWeak_shift x).symm
    have hmeas_shift2 : Measurable (FiniteDependence.Coloring.shift (q := 2)) := measurable_shift 2
    have hmeas_shift3 : Measurable (FiniteDependence.Coloring.shift (q := 3)) := measurable_shift 3
    change ((μ3 : Measure (ℤ → Fin 3)).map (FiniteDependence.Coloring.shift (q := 3)))
      = (μ3 : Measure (ℤ → Fin 3))
    have hstat2' :
        ((μ2 : Measure (ℤ → Fin 2)).map (FiniteDependence.Coloring.shift (q := 2)))
          = (μ2 : Measure (ℤ → Fin 2)) := hstat2
    calc
      ((μ3 : Measure (ℤ → Fin 3)).map (FiniteDependence.Coloring.shift (q := 3)))
          = (((μ2 : Measure (ℤ → Fin 2)).map greedyThreeFromWeak).map
              (FiniteDependence.Coloring.shift (q := 3))) := by
                rfl
      _ = (μ2 : Measure (ℤ → Fin 2)).map ((FiniteDependence.Coloring.shift (q := 3)) ∘ greedyThreeFromWeak) := by
            simpa using (Measure.map_map (μ := (μ2 : Measure (ℤ → Fin 2))) hmeas_shift3
              measurable_greedyThreeFromWeak)
      _ = (μ2 : Measure (ℤ → Fin 2)).map (greedyThreeFromWeak ∘ (FiniteDependence.Coloring.shift (q := 2))) := by
            simp [hcomm]
      _ = (((μ2 : Measure (ℤ → Fin 2)).map (FiniteDependence.Coloring.shift (q := 2))).map greedyThreeFromWeak) := by
            symm
            simpa using (Measure.map_map (μ := (μ2 : Measure (ℤ → Fin 2))) measurable_greedyThreeFromWeak
              hmeas_shift2)
      _ = (μ2 : Measure (ℤ → Fin 2)).map greedyThreeFromWeak := by
            simp [hstat2']
      _ = (μ3 : Measure (ℤ → Fin 3)) := rfl
  · have hdep3' : FiniteDependence.Coloring.IsKDependent (q := 2) μ2 3 := by
      simpa [IsKDependentCut, FiniteDependence.Coloring.IsKDependent] using hdep3
    have hkdepMap : FiniteDependence.Coloring.IsKDependent (q := 3) μ3 6 := by
      intro i
      have hbase :
          Indep (FiniteDependence.Coloring.pastMeasurableSpace (q := 2) (i + 3))
            (FiniteDependence.Coloring.futureMeasurableSpace (q := 2) (i + 3) 3)
            (μ := (μ2 : Measure (ℤ → Fin 2))) := hdep3' (i + 3)
      have hcomap :
          Indep ((FiniteDependence.Coloring.pastMeasurableSpace (q := 3) i).comap greedyThreeFromWeak)
            ((FiniteDependence.Coloring.futureMeasurableSpace (q := 3) i 6).comap greedyThreeFromWeak)
              (μ := (μ2 : Measure (ℤ → Fin 2))) := by
        have h1 :
            Indep ((FiniteDependence.Coloring.pastMeasurableSpace (q := 3) i).comap greedyThreeFromWeak)
              (FiniteDependence.Coloring.futureMeasurableSpace (q := 2) (i + 3) 3)
                (μ := (μ2 : Measure (ℤ → Fin 2))) :=
          indep_of_indep_of_le_left hbase (comap_past_le_greedy3 (i := i))
        exact indep_of_indep_of_le_right h1 (comap_future_le_greedy3 (i := i))
      have hmap :
          Indep (FiniteDependence.Coloring.pastMeasurableSpace (q := 3) i)
            (FiniteDependence.Coloring.futureMeasurableSpace (q := 3) i 6)
            (μ :=
              @Measure.map (ℤ → Fin 2) (ℤ → Fin 3) MeasurableSpace.pi MeasurableSpace.pi greedyThreeFromWeak
                (μ2 : Measure (ℤ → Fin 2))) := by
        refine
          indep_map_of_indep_comap (mΩ' := (MeasurableSpace.pi : MeasurableSpace (ℤ → Fin 3)))
            (μ := (μ2 : Measure (ℤ → Fin 2))) (f := greedyThreeFromWeak)
            (hf := measurable_greedyThreeFromWeak.aemeasurable) (hm₁ := ?_) (hm₂ := ?_) hcomap
        · simpa using pastMeasurableSpace_le (q := 3) i
        · simpa using futureMeasurableSpace_le (q := 3) i 6
      simpa [μ3, ProbabilityMeasure.map] using hmap
    simpa [IsKDependentCut, FiniteDependence.Coloring.IsKDependent] using hkdepMap
  · have hsub :
      {x : ℤ → Fin 2 | IsWeakTwoColoring x}
        ⊆ greedyThreeFromWeak ⁻¹' {y : ℤ → Fin 3 | IsGreedyThreeColoring y} := by
      intro x hx
      exact greedyThreeFromWeak_isGreedy_of_isWeak x hx
    have hpre :
        (μ2 : Measure (ℤ → Fin 2))
          (greedyThreeFromWeak ⁻¹' {y : ℤ → Fin 3 | IsGreedyThreeColoring y}) = 1 := by
      have hle :
          (μ2 : Measure (ℤ → Fin 2)) {x : ℤ → Fin 2 | IsWeakTwoColoring x}
            ≤ (μ2 : Measure (ℤ → Fin 2))
                (greedyThreeFromWeak ⁻¹' {y : ℤ → Fin 3 | IsGreedyThreeColoring y}) :=
        measure_mono hsub
      have hle1 :
          (μ2 : Measure (ℤ → Fin 2))
            (greedyThreeFromWeak ⁻¹' {y : ℤ → Fin 3 | IsGreedyThreeColoring y}) ≤ 1 := by
        have : (μ2 : Measure (ℤ → Fin 2))
            (greedyThreeFromWeak ⁻¹' {y : ℤ → Fin 3 | IsGreedyThreeColoring y})
              ≤ (μ2 : Measure (ℤ → Fin 2)) Set.univ :=
          measure_mono (subset_univ _)
        simpa using this
      have hge : (1 : ENNReal) ≤
          (μ2 : Measure (ℤ → Fin 2))
            (greedyThreeFromWeak ⁻¹' {y : ℤ → Fin 3 | IsGreedyThreeColoring y}) := by
        simpa [hweak2] using hle
      exact le_antisymm hle1 hge
    have hmap :
        (μ3 : Measure (ℤ → Fin 3)) {y : ℤ → Fin 3 | IsGreedyThreeColoring y}
          = (μ2 : Measure (ℤ → Fin 2))
              (greedyThreeFromWeak ⁻¹' {y : ℤ → Fin 3 | IsGreedyThreeColoring y}) := by
      simpa [μ3] using
        (ProbabilityMeasure.map_apply' μ2 measurable_greedyThreeFromWeak.aemeasurable
          FiniteDependence.measurableSet_isGreedyThreeColoring)
    exact hmap.trans hpre

/-! ## Reduction greedy-3 → MIS -/

private def misFromGreedyThree (c : ℤ → Fin 3) : ℤ → Fin 2 :=
  fun i => if c i = 0 then 1 else 0

private lemma fin3_eq_two_of_ne_zero_of_ne_one (a : Fin 3) (h0 : a ≠ 0) (h1 : a ≠ 1) : a = 2 := by
  fin_cases a <;> simp at h0 h1 ⊢

private lemma measurable_misFromGreedyThree : Measurable misFromGreedyThree := by
  classical
  refine measurable_pi_lambda _ (fun i => ?_)
  have h0 : Measurable fun c : ℤ → Fin 3 => c i := by
    simpa using (measurable_pi_apply (a := i))
  have hset : MeasurableSet {c : ℤ → Fin 3 | c i = (0 : Fin 3)} := by
    simpa [Set.preimage, Set.mem_singleton_iff] using
      (measurableSet_singleton (0 : Fin 3)).preimage h0
  exact Measurable.ite hset measurable_const measurable_const

private lemma misFromGreedyThree_shift (c : ℤ → Fin 3) :
    misFromGreedyThree (FiniteDependence.Coloring.shift (q := 3) c)
      = FiniteDependence.Coloring.shift (q := 2) (misFromGreedyThree c) := by
  ext i
  simp [misFromGreedyThree, FiniteDependence.Coloring.shift, FiniteDependence.shift]

private lemma misFromGreedyThree_isMIS_of_isGreedy (c : ℤ → Fin 3) (hc : IsGreedyThreeColoring c) :
    FiniteDependence.IsMIS (misFromGreedyThree c) := by
  rcases hc with ⟨hcol, hone, htwo⟩
  refine ⟨?_, ?_⟩
  · intro i hi
    rcases hi with ⟨hleft, hright⟩
    have hci0 : c i = 0 := by
      by_cases h : c i = 0
      · exact h
      · simp [misFromGreedyThree, h] at hleft
    have hci10 : c (i + 1) = 0 := by
      by_cases h : c (i + 1) = 0
      · exact h
      · simp [misFromGreedyThree, h] at hright
    exact (hcol i) (by simpa [hci0] using hci10.symm)
  · intro i hi
    rcases hi with ⟨h0, h1, h2⟩
    have hci_ne0 : c i ≠ 0 := by
      intro h
      simp [misFromGreedyThree, h] at h0
    have hcim1_ne0 : c (i + 1) ≠ 0 := by
      intro h
      simp [misFromGreedyThree, h] at h1
    have hcim2_ne0 : c (i + 2) ≠ 0 := by
      intro h
      simp [misFromGreedyThree, h] at h2
    have hmid_cases : c (i + 1) = 1 ∨ c (i + 1) = 2 := by
      by_cases hmid1 : c (i + 1) = 1
      · exact Or.inl hmid1
      · exact Or.inr (fin3_eq_two_of_ne_zero_of_ne_one (c (i + 1)) hcim1_ne0 hmid1)
    cases hmid_cases with
    | inl hmid1 =>
        have hnb := hone (i + 1) hmid1
        cases hnb with
        | inl hl =>
            exact hci_ne0 (by simpa [add_assoc] using hl)
        | inr hr =>
            exact hcim2_ne0 (by simpa [add_assoc] using hr)
    | inr hmid2 =>
        have hnb := (htwo (i + 1) hmid2).1
        cases hnb with
        | inl hl =>
            exact hci_ne0 (by simpa [add_assoc] using hl)
        | inr hr =>
            exact hcim2_ne0 (by simpa [add_assoc] using hr)

private lemma comap_past_le_misGreedy (i : ℤ) :
    (FiniteDependence.Coloring.pastMeasurableSpace (q := 2) i).comap misFromGreedyThree
      ≤ FiniteDependence.Coloring.pastMeasurableSpace (q := 3) i := by
  classical
  unfold FiniteDependence.Coloring.pastMeasurableSpace FiniteDependence.pastMeasurableSpace
  simp [MeasurableSpace.comap_iSup, MeasurableSpace.comap_comp]
  intro a ha
  have hm : Measurable[FiniteDependence.Coloring.pastMeasurableSpace (q := 3) i]
      fun c : ℤ → Fin 3 => c a :=
    measurable_apply_past (q := 3) (i := i) (j := a) ha
  have hset : MeasurableSet[FiniteDependence.Coloring.pastMeasurableSpace (q := 3) i]
      {c : ℤ → Fin 3 | c a = (0 : Fin 3)} := by
    simpa [Set.preimage, Set.mem_singleton_iff] using
      (measurableSet_singleton (0 : Fin 3)).preimage hm
  have hmeas : Measurable[FiniteDependence.Coloring.pastMeasurableSpace (q := 3) i]
      fun c : ℤ → Fin 3 => misFromGreedyThree c a := by
    exact Measurable.ite hset measurable_const measurable_const
  simpa [Function.comp, misFromGreedyThree] using hmeas.comap_le

private lemma comap_future_le_misGreedy (i : ℤ) :
    (FiniteDependence.Coloring.futureMeasurableSpace (q := 2) i 5).comap misFromGreedyThree
      ≤ FiniteDependence.Coloring.futureMeasurableSpace (q := 3) i 5 := by
  classical
  unfold FiniteDependence.Coloring.futureMeasurableSpace FiniteDependence.futureMeasurableSpace
  simp [MeasurableSpace.comap_iSup, MeasurableSpace.comap_comp]
  intro a ha
  have hm : Measurable[FiniteDependence.Coloring.futureMeasurableSpace (q := 3) i 5]
      fun c : ℤ → Fin 3 => c a :=
    measurable_apply_future (q := 3) (i := i) (k := 5) (j := a) ha
  have hset : MeasurableSet[FiniteDependence.Coloring.futureMeasurableSpace (q := 3) i 5]
      {c : ℤ → Fin 3 | c a = (0 : Fin 3)} := by
    simpa [Set.preimage, Set.mem_singleton_iff] using
      (measurableSet_singleton (0 : Fin 3)).preimage hm
  have hmeas : Measurable[FiniteDependence.Coloring.futureMeasurableSpace (q := 3) i 5]
      fun c : ℤ → Fin 3 => misFromGreedyThree c a := by
    exact Measurable.ite hset measurable_const measurable_const
  simpa [Function.comp, misFromGreedyThree] using hmeas.comap_le

/-! ## Non-existence at dependence range 5 -/

/-- No stationary `5`-dependent greedy proper `3`-coloring law exists on `ℤ`. -/
theorem not_exists_stationary_fiveDependent_greedyThreeColoring :
    ¬ ∃ μ : ProbabilityMeasure (ℤ → Fin 3),
        IsStationary μ ∧
        IsKDependentCut μ 5 ∧
        (μ : Measure (ℤ → Fin 3)) {x | IsGreedyThreeColoring x} = 1 := by
  intro h
  rcases h with ⟨μ3, hstat3, hdep5, hgreedy⟩
  let μMIS : ProbabilityMeasure (ℤ → Fin 2) := μ3.map measurable_misFromGreedyThree.aemeasurable

  have hstatMIS : IsStationary μMIS := by
    have hcomm :
        (FiniteDependence.Coloring.shift (q := 2)) ∘ misFromGreedyThree
          = misFromGreedyThree ∘ (FiniteDependence.Coloring.shift (q := 3)) := by
      funext c
      simpa [Function.comp] using (misFromGreedyThree_shift c).symm
    have hmeas_shift2 : Measurable (FiniteDependence.Coloring.shift (q := 2)) := measurable_shift 2
    have hmeas_shift3 : Measurable (FiniteDependence.Coloring.shift (q := 3)) := measurable_shift 3
    change (((μMIS : ProbabilityMeasure (ℤ → Fin 2)) : Measure (ℤ → Fin 2)).map
      (FiniteDependence.Coloring.shift (q := 2)))
      = ((μMIS : ProbabilityMeasure (ℤ → Fin 2)) : Measure (ℤ → Fin 2))
    have hstat3' :
        ((μ3 : Measure (ℤ → Fin 3)).map (FiniteDependence.Coloring.shift (q := 3)))
          = (μ3 : Measure (ℤ → Fin 3)) := hstat3
    calc
      (((μMIS : ProbabilityMeasure (ℤ → Fin 2)) : Measure (ℤ → Fin 2)).map
          (FiniteDependence.Coloring.shift (q := 2)))
          = (((μ3 : Measure (ℤ → Fin 3)).map misFromGreedyThree).map
              (FiniteDependence.Coloring.shift (q := 2))) := by
                rfl
      _ = (μ3 : Measure (ℤ → Fin 3)).map ((FiniteDependence.Coloring.shift (q := 2)) ∘ misFromGreedyThree) := by
            simpa using (Measure.map_map (μ := (μ3 : Measure (ℤ → Fin 3))) hmeas_shift2 measurable_misFromGreedyThree)
      _ = (μ3 : Measure (ℤ → Fin 3)).map (misFromGreedyThree ∘ (FiniteDependence.Coloring.shift (q := 3))) := by
            simp [hcomm]
      _ = (((μ3 : Measure (ℤ → Fin 3)).map (FiniteDependence.Coloring.shift (q := 3))).map misFromGreedyThree) := by
            symm
            simpa using (Measure.map_map (μ := (μ3 : Measure (ℤ → Fin 3))) measurable_misFromGreedyThree hmeas_shift3)
      _ = (μ3 : Measure (ℤ → Fin 3)).map misFromGreedyThree := by
            simp [hstat3']
      _ = ((μMIS : ProbabilityMeasure (ℤ → Fin 2)) : Measure (ℤ → Fin 2)) := rfl

  have hdep5' : FiniteDependence.Coloring.IsKDependent (q := 3) μ3 5 := by
    simpa [IsKDependentCut, FiniteDependence.Coloring.IsKDependent] using hdep5

  have hdepMIS : IsKDependentCut μMIS 5 := by
    have hkdepMap : FiniteDependence.Coloring.IsKDependent (q := 2) μMIS 5 := by
      intro i
      have hbase :
          Indep (FiniteDependence.Coloring.pastMeasurableSpace (q := 3) i)
            (FiniteDependence.Coloring.futureMeasurableSpace (q := 3) i 5)
            (μ := (μ3 : Measure (ℤ → Fin 3))) := hdep5' i
      have hcomap :
          Indep ((FiniteDependence.Coloring.pastMeasurableSpace (q := 2) i).comap misFromGreedyThree)
            ((FiniteDependence.Coloring.futureMeasurableSpace (q := 2) i 5).comap misFromGreedyThree)
              (μ := (μ3 : Measure (ℤ → Fin 3))) := by
        have h1 :
            Indep ((FiniteDependence.Coloring.pastMeasurableSpace (q := 2) i).comap misFromGreedyThree)
              (FiniteDependence.Coloring.futureMeasurableSpace (q := 3) i 5)
                (μ := (μ3 : Measure (ℤ → Fin 3))) :=
          indep_of_indep_of_le_left hbase (comap_past_le_misGreedy (i := i))
        exact indep_of_indep_of_le_right h1 (comap_future_le_misGreedy (i := i))
      have hmap :
          Indep (FiniteDependence.Coloring.pastMeasurableSpace (q := 2) i)
            (FiniteDependence.Coloring.futureMeasurableSpace (q := 2) i 5)
            (μ :=
              @Measure.map (ℤ → Fin 3) (ℤ → Fin 2) MeasurableSpace.pi MeasurableSpace.pi misFromGreedyThree
                (μ3 : Measure (ℤ → Fin 3))) := by
        refine
          indep_map_of_indep_comap (mΩ' := (MeasurableSpace.pi : MeasurableSpace (ℤ → Fin 2)))
            (μ := (μ3 : Measure (ℤ → Fin 3))) (f := misFromGreedyThree)
            (hf := measurable_misFromGreedyThree.aemeasurable) (hm₁ := ?_) (hm₂ := ?_) hcomap
        · simpa using pastMeasurableSpace_le (q := 2) i
        · simpa using futureMeasurableSpace_le (q := 2) i 5
      simpa [μMIS, ProbabilityMeasure.map] using hmap
    simpa [IsKDependentCut, FiniteDependence.Coloring.IsKDependent] using hkdepMap

  have hMISsupport :
      ((μMIS : Measure (ℤ → Fin 2)) {x : ℤ → Fin 2 | FiniteDependence.IsMIS x} = 1) := by
    have hsub :
        {x : ℤ → Fin 3 | IsGreedyThreeColoring x}
          ⊆ misFromGreedyThree ⁻¹' {x : ℤ → Fin 2 | FiniteDependence.IsMIS x} := by
      intro x hx
      exact misFromGreedyThree_isMIS_of_isGreedy x hx
    have hpre :
        (μ3 : Measure (ℤ → Fin 3))
          (misFromGreedyThree ⁻¹' {x : ℤ → Fin 2 | FiniteDependence.IsMIS x}) = 1 := by
      have hle :
          (μ3 : Measure (ℤ → Fin 3)) {x : ℤ → Fin 3 | IsGreedyThreeColoring x}
            ≤ (μ3 : Measure (ℤ → Fin 3))
                (misFromGreedyThree ⁻¹' {x : ℤ → Fin 2 | FiniteDependence.IsMIS x}) :=
        measure_mono hsub
      have hle1 :
          (μ3 : Measure (ℤ → Fin 3))
            (misFromGreedyThree ⁻¹' {x : ℤ → Fin 2 | FiniteDependence.IsMIS x}) ≤ 1 := by
        have : (μ3 : Measure (ℤ → Fin 3))
            (misFromGreedyThree ⁻¹' {x : ℤ → Fin 2 | FiniteDependence.IsMIS x})
              ≤ (μ3 : Measure (ℤ → Fin 3)) Set.univ :=
          measure_mono (subset_univ _)
        simpa using this
      have hge : (1 : ENNReal) ≤
          (μ3 : Measure (ℤ → Fin 3))
            (misFromGreedyThree ⁻¹' {x : ℤ → Fin 2 | FiniteDependence.IsMIS x}) := by
        simpa [hgreedy] using hle
      exact le_antisymm hle1 hge
    have hmap :
        (μMIS : Measure (ℤ → Fin 2)) {x : ℤ → Fin 2 | FiniteDependence.IsMIS x}
          = (μ3 : Measure (ℤ → Fin 3))
              (misFromGreedyThree ⁻¹' {x : ℤ → Fin 2 | FiniteDependence.IsMIS x}) := by
      simpa [μMIS] using
        (ProbabilityMeasure.map_apply' μ3 measurable_misFromGreedyThree.aemeasurable
          FiniteDependence.measurableSet_isMIS)
    exact hmap.trans hpre

  have hexMIS5 : ExistsStationaryKDependentMIS 5 := by
    refine ⟨μMIS, ?_⟩
    exact ⟨hstatMIS, hdepMIS, hMISsupport⟩
  exact FiniteDependence.LowerBoundBridge.not_exists_stationary_fiveDependent_MIS hexMIS5

end FiniteDependence.Coloring
