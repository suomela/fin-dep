import FiniteDependence.API.Definitions
import FiniteDependence.Core.MeasurablePredicates
import FiniteDependence.Coloring.Existence
import FiniteDependence.Coloring.MeasureHelpers
import FiniteDependence.MIS.LowerBounds.K5.Bridge

import Mathlib.MeasureTheory.Measure.Map
import Mathlib.MeasureTheory.MeasurableSpace.Prod
import Mathlib.Tactic

/-!
# Weak 2-coloring threshold on `ℤ`

We formalize the threshold for binary weak 2-colorings (forbidden patterns `000` and `111`):

* existence of a stationary `3`-dependent law;
* non-existence of a stationary `2`-dependent law.

The lower bound uses an explicit local factor to MIS and the already-proved theorem
`LowerBoundBridge.not_exists_stationary_fiveDependent_MIS`.
-/

namespace FiniteDependence

open MeasureTheory ProbabilityTheory Set

namespace WeakTwo

/-! ## Existence: stationary 3-dependent weak-2-coloring -/

private def ascentPair (p : Fin 3 × Fin 3) : Fin 2 :=
  if p.1 < p.2 then 1 else 0

private def weakTwoFromThree (c : ℤ → Fin 3) : ℤ → Fin 2 :=
  fun i => ascentPair (c i, c (i + 1))

private lemma measurable_ascentPair : Measurable ascentPair := by
  classical
  simpa [ascentPair] using
    (Measurable.of_discrete : Measurable (fun p : Fin 3 × Fin 3 => if p.1 < p.2 then (1 : Fin 2) else 0))

private lemma measurable_weakTwoFromThree_at {m : MeasurableSpace (ℤ → Fin 3)} (i : ℤ)
    (h0 : Measurable[m] fun c : ℤ → Fin 3 => c i)
    (h1 : Measurable[m] fun c : ℤ → Fin 3 => c (i + 1)) :
    Measurable[m] fun c : ℤ → Fin 3 => weakTwoFromThree c i := by
  have hpair : Measurable[m] fun c : ℤ → Fin 3 => (c i, c (i + 1)) := h0.prodMk h1
  simpa [weakTwoFromThree] using measurable_ascentPair.comp hpair

private lemma measurable_weakTwoFromThree : Measurable weakTwoFromThree := by
  classical
  refine measurable_pi_lambda _ (fun i => ?_)
  exact measurable_weakTwoFromThree_at (m := inferInstance) (i := i)
    (h0 := by simpa using (measurable_pi_apply (a := i)))
    (h1 := by simpa using (measurable_pi_apply (a := i + 1)))

private def weakTwoOffsets : Fin 2 → ℤ
  | 0 => 0
  | 1 => 1

private lemma measurable_weakTwoFromThree_local {m : MeasurableSpace (ℤ → Fin 3)} (i : ℤ)
    (hcoords : ∀ t : Fin 2, Measurable[m] fun c : ℤ → Fin 3 => c (i + weakTwoOffsets t)) :
    Measurable[m] fun c : ℤ → Fin 3 => weakTwoFromThree c i := by
  refine measurable_weakTwoFromThree_at (m := m) (i := i)
    (h0 := ?_) (h1 := ?_)
  · simpa [weakTwoOffsets] using hcoords 0
  · simpa [weakTwoOffsets] using hcoords 1

private lemma weakTwoFromThree_shift (c : ℤ → Fin 3) :
    weakTwoFromThree (FiniteDependence.Coloring.shift (q := 3) c)
      = FiniteDependence.Coloring.shift (q := 2) (weakTwoFromThree c) := by
  ext i
  simp [weakTwoFromThree, ascentPair, FiniteDependence.Coloring.shift, FiniteDependence.shift,
    add_assoc, add_left_comm, add_comm]

private lemma ascent_no111_local :
    ∀ a b c d : Fin 3,
      ¬(ascentPair (a, b) = 1 ∧ ascentPair (b, c) = 1 ∧ ascentPair (c, d) = 1) := by
  decide

private lemma ascent_no000_local :
    ∀ a b c d : Fin 3, a ≠ b → b ≠ c → c ≠ d →
      ¬(ascentPair (a, b) = 0 ∧ ascentPair (b, c) = 0 ∧ ascentPair (c, d) = 0) := by
  decide

private lemma weakTwoFromThree_isWeak_of_isColoring (c : ℤ → Fin 3) (hc : FiniteDependence.Coloring.IsColoring (q := 3) c) :
    IsWeakTwoColoring (weakTwoFromThree c) := by
  refine ⟨?_, ?_⟩
  · intro i hi
    rcases hi with ⟨h0, h1, h2⟩
    have hne01 : c i ≠ c (i + 1) := hc i
    have hne12 : c (i + 1) ≠ c (i + 2) := by simpa [add_assoc] using hc (i + 1)
    have hne23 : c (i + 2) ≠ c (i + 3) := by simpa [add_assoc] using hc (i + 2)
    have hloc := ascent_no000_local (a := c i) (b := c (i + 1)) (c := c (i + 2)) (d := c (i + 3))
      hne01 hne12 hne23
    have ha0 : ascentPair (c i, c (i + 1)) = 0 := by simpa [weakTwoFromThree] using h0
    have ha1 : ascentPair (c (i + 1), c (i + 2)) = 0 := by
      simpa [weakTwoFromThree, add_assoc] using h1
    have ha2 : ascentPair (c (i + 2), c (i + 3)) = 0 := by
      simpa [weakTwoFromThree, add_assoc] using h2
    exact hloc ⟨ha0, ha1, ha2⟩
  · intro i hi
    rcases hi with ⟨h0, h1, h2⟩
    have hloc := ascent_no111_local (a := c i) (b := c (i + 1)) (c := c (i + 2)) (d := c (i + 3))
    have ha0 : ascentPair (c i, c (i + 1)) = 1 := by simpa [weakTwoFromThree] using h0
    have ha1 : ascentPair (c (i + 1), c (i + 2)) = 1 := by
      simpa [weakTwoFromThree, add_assoc] using h1
    have ha2 : ascentPair (c (i + 2), c (i + 3)) = 1 := by
      simpa [weakTwoFromThree, add_assoc] using h2
    exact hloc ⟨ha0, ha1, ha2⟩

private lemma comap_past_le_weak (i : ℤ) :
    (FiniteDependence.Coloring.pastMeasurableSpace (q := 2) i).comap weakTwoFromThree
      ≤ FiniteDependence.Coloring.pastMeasurableSpace (q := 3) (i + 1) := by
  simpa [weakTwoOffsets] using
    (FiniteDependence.Coloring.comap_past_le_of_local
      (q := 3) (q' := 2) (f := weakTwoFromThree) (o := weakTwoOffsets) (r := 1)
      (hlocal := measurable_weakTwoFromThree_local)
      (hupper := by
        intro t
        fin_cases t <;> decide)
      i)

private lemma comap_future_le_weak (i : ℤ) :
    (FiniteDependence.Coloring.futureMeasurableSpace (q := 2) i 3).comap weakTwoFromThree
      ≤ FiniteDependence.Coloring.futureMeasurableSpace (q := 3) (i + 1) 2 := by
  simpa [weakTwoOffsets] using
    (FiniteDependence.Coloring.comap_future_le_of_local
      (q := 3) (q' := 2) (f := weakTwoFromThree) (o := weakTwoOffsets) (r := 1) (k := 2)
      (k' := 3) (hlocal := measurable_weakTwoFromThree_local)
      (hlower := by
        intro t
        fin_cases t <;> decide)
      i)

private lemma comap_future_le_weak_k2 (i : ℤ) :
    (FiniteDependence.Coloring.futureMeasurableSpace (q := 2) i 2).comap weakTwoFromThree
      ≤ FiniteDependence.Coloring.futureMeasurableSpace (q := 3) (i + 1) 1 := by
  simpa [weakTwoOffsets] using
    (FiniteDependence.Coloring.comap_future_le_of_local
      (q := 3) (q' := 2) (f := weakTwoFromThree) (o := weakTwoOffsets) (r := 1) (k := 1)
      (k' := 2) (hlocal := measurable_weakTwoFromThree_local)
      (hlower := by
        intro t
        fin_cases t <;> decide)
      i)

/-- A stationary `3`-dependent weak-2-coloring law exists on `ℤ`. -/
theorem exists_stationary_threeDependent_weakTwoColoring :
    ExistsStationaryKDependentWeakTwoColoring 3 := by
  classical
  rcases FiniteDependence.Coloring.exists_stationary_twoDependent_threeColoring with
    ⟨μ3, hstat3, hkdep3, hcol3⟩
  let μ : ProbabilityMeasure (ℤ → Fin 2) := μ3.map measurable_weakTwoFromThree.aemeasurable
  refine ⟨μ, ?_⟩
  refine ⟨?_, ?_, ?_⟩
  · -- Stationarity of the factor.
    have hcomm :
        (FiniteDependence.Coloring.shift (q := 2)) ∘ weakTwoFromThree
          = weakTwoFromThree ∘ (FiniteDependence.Coloring.shift (q := 3)) := by
      funext c
      simpa [Function.comp] using (weakTwoFromThree_shift c).symm
    simpa [μ] using
      (FiniteDependence.Coloring.isStationary_map_of_comm
        (hf := measurable_weakTwoFromThree)
        (hcomm := hcomm) (hstat := hstat3))
  · -- 3-dependence from 2-dependence and one-sided radius 1.
    have hkdepMap : FiniteDependence.Coloring.IsKDependent (q := 2) μ 3 :=
      FiniteDependence.Coloring.isKDependent_map_of_past_future
        (hf := measurable_weakTwoFromThree.aemeasurable) (hdep := hkdep3)
        (cut := fun i => i + 1) (hpast := comap_past_le_weak)
        (hfuture := comap_future_le_weak)
    simpa [IsKDependentCut, FiniteDependence.Coloring.IsKDependent] using hkdepMap
  · -- Weak-2 support from proper-coloring support.
    have hpre :
        (μ3 : Measure (ℤ → Fin 3)) (weakTwoFromThree ⁻¹' {x : ℤ → Fin 2 | IsWeakTwoColoring x}) = 1 := by
      have hsub :
          {c : ℤ → Fin 3 | FiniteDependence.Coloring.IsColoring (q := 3) c}
            ⊆ weakTwoFromThree ⁻¹' {x : ℤ → Fin 2 | IsWeakTwoColoring x} := by
        intro c hc
        exact weakTwoFromThree_isWeak_of_isColoring c hc
      have hle :
          (μ3 : Measure (ℤ → Fin 3)) {c : ℤ → Fin 3 | FiniteDependence.Coloring.IsColoring (q := 3) c}
            ≤ (μ3 : Measure (ℤ → Fin 3))
                (weakTwoFromThree ⁻¹' {x : ℤ → Fin 2 | IsWeakTwoColoring x}) :=
        measure_mono hsub
      have hle1 :
          (μ3 : Measure (ℤ → Fin 3)) (weakTwoFromThree ⁻¹' {x : ℤ → Fin 2 | IsWeakTwoColoring x}) ≤ 1 := by
        have : (μ3 : Measure (ℤ → Fin 3))
            (weakTwoFromThree ⁻¹' {x : ℤ → Fin 2 | IsWeakTwoColoring x})
              ≤ (μ3 : Measure (ℤ → Fin 3)) Set.univ := measure_mono (subset_univ _)
        simpa using this
      have hcol : (μ3 : Measure (ℤ → Fin 3))
          {c : ℤ → Fin 3 | FiniteDependence.Coloring.IsColoring (q := 3) c} = 1 := hcol3
      have hge : (1 : ENNReal) ≤
          (μ3 : Measure (ℤ → Fin 3)) (weakTwoFromThree ⁻¹' {x : ℤ → Fin 2 | IsWeakTwoColoring x}) := by
        simpa [hcol] using hle
      exact le_antisymm hle1 hge
    have hmap :
        (μ : Measure (ℤ → Fin 2)) {x : ℤ → Fin 2 | IsWeakTwoColoring x}
          = (μ3 : Measure (ℤ → Fin 3)) (weakTwoFromThree ⁻¹' {x : ℤ → Fin 2 | IsWeakTwoColoring x}) := by
      simpa [μ] using
        (ProbabilityMeasure.map_apply' μ3 measurable_weakTwoFromThree.aemeasurable
          FiniteDependence.measurableSet_isWeakTwoColoring)
    calc
      (μ : Measure (ℤ → Fin 2)) {x : ℤ → Fin 2 | IsWeakTwoColoring x}
          = (μ3 : Measure (ℤ → Fin 3)) (weakTwoFromThree ⁻¹' {x : ℤ → Fin 2 | IsWeakTwoColoring x}) := hmap
      _ = 1 := hpre

/-! ## Reduction map from weak-2-colorings to MIS -/

private def misFactor4 : Fin 2 → Fin 2 → Fin 2 → Fin 2 → Fin 2
  | 0, 0, 1, 0 => 1
  | 0, 0, 1, 1 => 1
  | 1, 0, 1, 0 => 1
  | 1, 0, 1, 1 => 1
  | 1, 1, 0, 0 => 1
  | _, _, _, _ => 0

private def misFromWeak (x : ℤ → Fin 2) : ℤ → Fin 2 :=
  fun i => misFactor4 (x i) (x (i + 1)) (x (i + 2)) (x (i + 3))

private def misFactor4Tuple (t : Fin 2 × Fin 2 × Fin 2 × Fin 2) : Fin 2 :=
  misFactor4 t.1 t.2.1 t.2.2.1 t.2.2.2

private lemma measurable_misFactor4Tuple : Measurable misFactor4Tuple := by
  classical
  simpa [misFactor4Tuple] using (Measurable.of_discrete : Measurable misFactor4Tuple)

private lemma measurable_misFromWeak_at {m : MeasurableSpace (ℤ → Fin 2)} (i : ℤ)
    (h0 : Measurable[m] fun x : ℤ → Fin 2 => x i)
    (h1 : Measurable[m] fun x : ℤ → Fin 2 => x (i + 1))
    (h2 : Measurable[m] fun x : ℤ → Fin 2 => x (i + 2))
    (h3 : Measurable[m] fun x : ℤ → Fin 2 => x (i + 3)) :
    Measurable[m] fun x : ℤ → Fin 2 => misFromWeak x i := by
  have htuple : Measurable[m] fun x : ℤ → Fin 2 => (x i, x (i + 1), x (i + 2), x (i + 3)) :=
    h0.prodMk (h1.prodMk (h2.prodMk h3))
  simpa [misFromWeak, misFactor4Tuple] using measurable_misFactor4Tuple.comp htuple

private lemma measurable_misFromWeak : Measurable misFromWeak := by
  classical
  refine measurable_pi_lambda _ (fun i => ?_)
  exact measurable_misFromWeak_at (m := inferInstance) (i := i)
    (h0 := by simpa using (measurable_pi_apply (a := i)))
    (h1 := by simpa using (measurable_pi_apply (a := i + 1)))
    (h2 := by simpa using (measurable_pi_apply (a := i + 2)))
    (h3 := by simpa using (measurable_pi_apply (a := i + 3)))

private def fourBlockOffsets : Fin 4 → ℤ
  | 0 => 0
  | 1 => 1
  | 2 => 2
  | 3 => 3

private lemma measurable_misFromWeak_local {m : MeasurableSpace (ℤ → Fin 2)} (i : ℤ)
    (hcoords : ∀ t : Fin 4, Measurable[m] fun x : ℤ → Fin 2 => x (i + fourBlockOffsets t)) :
    Measurable[m] fun x : ℤ → Fin 2 => misFromWeak x i := by
  refine measurable_misFromWeak_at (m := m) (i := i)
    (h0 := ?_) (h1 := ?_) (h2 := ?_) (h3 := ?_)
  · simpa [fourBlockOffsets] using hcoords 0
  · simpa [fourBlockOffsets] using hcoords 1
  · simpa [fourBlockOffsets] using hcoords 2
  · simpa [fourBlockOffsets] using hcoords 3

private lemma misFromWeak_shift (x : ℤ → Fin 2) :
    misFromWeak (FiniteDependence.Coloring.shift (q := 2) x)
      = FiniteDependence.Coloring.shift (q := 2) (misFromWeak x) := by
  ext i
  simp [misFromWeak, FiniteDependence.Coloring.shift, FiniteDependence.shift,
    add_assoc, add_left_comm, add_comm]

private def goodTriple (a b c : Fin 2) : Prop :=
  ¬(a = 0 ∧ b = 0 ∧ c = 0) ∧ ¬(a = 1 ∧ b = 1 ∧ c = 1)

private instance decGoodTriple (a b c : Fin 2) : Decidable (goodTriple a b c) := by
  unfold goodTriple
  infer_instance

private lemma mis_no11_local :
    ∀ a b c d e : Fin 2,
      goodTriple a b c → goodTriple b c d → goodTriple c d e →
        ¬(misFactor4 a b c d = 1 ∧ misFactor4 b c d e = 1) := by
  decide

private lemma mis_no000_local :
    ∀ a b c d e f : Fin 2,
      goodTriple a b c → goodTriple b c d → goodTriple c d e → goodTriple d e f →
        ¬(misFactor4 a b c d = 0 ∧ misFactor4 b c d e = 0 ∧ misFactor4 c d e f = 0) := by
  decide

private lemma goodTriple_of_isWeak (x : ℤ → Fin 2) (hx : IsWeakTwoColoring x) (i : ℤ) :
    goodTriple (x i) (x (i + 1)) (x (i + 2)) := by
  rcases hx with ⟨h000, h111⟩
  exact ⟨h000 i, h111 i⟩

private lemma misFromWeak_isMIS_of_isWeak (x : ℤ → Fin 2) (hx : IsWeakTwoColoring x) :
    IsMIS (misFromWeak x) := by
  refine ⟨?_, ?_⟩
  · intro i hi
    rcases hi with ⟨h0, h1⟩
    have hgt0 : goodTriple (x i) (x (i + 1)) (x (i + 2)) := goodTriple_of_isWeak x hx i
    have hgt1 : goodTriple (x (i + 1)) (x (i + 2)) (x (i + 3)) := by
      simpa [add_assoc] using (goodTriple_of_isWeak x hx (i + 1))
    have hgt2 : goodTriple (x (i + 2)) (x (i + 3)) (x (i + 4)) := by
      simpa [add_assoc] using (goodTriple_of_isWeak x hx (i + 2))
    have hloc := mis_no11_local
      (a := x i) (b := x (i + 1)) (c := x (i + 2)) (d := x (i + 3)) (e := x (i + 4))
      hgt0 hgt1 hgt2
    have hm0 : misFactor4 (x i) (x (i + 1)) (x (i + 2)) (x (i + 3)) = 1 := by
      simpa [misFromWeak] using h0
    have hm1 : misFactor4 (x (i + 1)) (x (i + 2)) (x (i + 3)) (x (i + 4)) = 1 := by
      simpa [misFromWeak, add_assoc] using h1
    exact hloc ⟨hm0, hm1⟩
  · intro i hi
    rcases hi with ⟨h0, h1, h2⟩
    have hgt0 : goodTriple (x i) (x (i + 1)) (x (i + 2)) := goodTriple_of_isWeak x hx i
    have hgt1 : goodTriple (x (i + 1)) (x (i + 2)) (x (i + 3)) := by
      simpa [add_assoc] using (goodTriple_of_isWeak x hx (i + 1))
    have hgt2 : goodTriple (x (i + 2)) (x (i + 3)) (x (i + 4)) := by
      simpa [add_assoc] using (goodTriple_of_isWeak x hx (i + 2))
    have hgt3 : goodTriple (x (i + 3)) (x (i + 4)) (x (i + 5)) := by
      simpa [add_assoc] using (goodTriple_of_isWeak x hx (i + 3))
    have hloc := mis_no000_local
      (a := x i) (b := x (i + 1)) (c := x (i + 2)) (d := x (i + 3))
      (e := x (i + 4)) (f := x (i + 5)) hgt0 hgt1 hgt2 hgt3
    have hm0 : misFactor4 (x i) (x (i + 1)) (x (i + 2)) (x (i + 3)) = 0 := by
      simpa [misFromWeak] using h0
    have hm1 : misFactor4 (x (i + 1)) (x (i + 2)) (x (i + 3)) (x (i + 4)) = 0 := by
      simpa [misFromWeak, add_assoc] using h1
    have hm2 : misFactor4 (x (i + 2)) (x (i + 3)) (x (i + 4)) (x (i + 5)) = 0 := by
      simpa [misFromWeak, add_assoc] using h2
    exact hloc ⟨hm0, hm1, hm2⟩

private lemma comap_past_le_mis (i : ℤ) :
    (FiniteDependence.Coloring.pastMeasurableSpace (q := 2) i).comap misFromWeak
      ≤ FiniteDependence.Coloring.pastMeasurableSpace (q := 2) (i + 3) := by
  simpa [fourBlockOffsets] using
    (FiniteDependence.Coloring.comap_past_le_of_local
      (q := 2) (q' := 2) (f := misFromWeak) (o := fourBlockOffsets) (r := 3)
      (hlocal := measurable_misFromWeak_local)
      (hupper := by
        intro t
        fin_cases t <;> decide)
      i)

private lemma comap_future_le_mis (i : ℤ) :
    (FiniteDependence.Coloring.futureMeasurableSpace (q := 2) i 5).comap misFromWeak
      ≤ FiniteDependence.Coloring.futureMeasurableSpace (q := 2) (i + 3) 2 := by
  simpa [fourBlockOffsets] using
    (FiniteDependence.Coloring.comap_future_le_of_local
      (q := 2) (q' := 2) (f := misFromWeak) (o := fourBlockOffsets) (r := 3) (k := 2)
      (k' := 5) (hlocal := measurable_misFromWeak_local)
      (hlower := by
        intro t
        fin_cases t <;> decide)
      i)

/-! ## Non-existence at dependence range 2 -/

/-- No stationary `2`-dependent weak-2-coloring law exists on `ℤ`. -/
theorem not_exists_stationary_twoDependent_weakTwoColoring :
    ¬ ExistsStationaryKDependentWeakTwoColoring 2 := by
  intro h
  rcases h with ⟨μ, hμ⟩
  rcases hμ with ⟨hstat, hdep, hweak⟩
  let μMIS : ProbabilityMeasure (ℤ → Fin 2) := μ.map measurable_misFromWeak.aemeasurable
  have hstatMIS : IsStationary μMIS := by
    have hcomm :
        (FiniteDependence.Coloring.shift (q := 2)) ∘ misFromWeak
          = misFromWeak ∘ (FiniteDependence.Coloring.shift (q := 2)) := by
      funext x
      simpa [Function.comp] using (misFromWeak_shift x).symm
    have hstat' : FiniteDependence.Coloring.IsStationary (q := 2) μ := by
      simpa [FiniteDependence.Coloring.IsStationary] using hstat
    simpa [μMIS, FiniteDependence.Coloring.IsStationary] using
      (FiniteDependence.Coloring.isStationary_map_of_comm
        (hf := measurable_misFromWeak)
        (hcomm := hcomm) (hstat := hstat'))
  have hdep2 : FiniteDependence.Coloring.IsKDependent (q := 2) μ 2 := by
    simpa [IsKDependentCut, FiniteDependence.Coloring.IsKDependent] using hdep
  have hdepMIS : IsKDependentCut μMIS 5 := by
    have hkdepMap : FiniteDependence.Coloring.IsKDependent (q := 2) μMIS 5 :=
      FiniteDependence.Coloring.isKDependent_map_of_past_future
        (hf := measurable_misFromWeak.aemeasurable) (hdep := hdep2)
        (cut := fun i => i + 3) (hpast := comap_past_le_mis)
        (hfuture := comap_future_le_mis)
    simpa [IsKDependentCut, FiniteDependence.Coloring.IsKDependent] using hkdepMap
  have hMISsupport :
      ((μMIS : Measure (ℤ → Fin 2)) {x : ℤ → Fin 2 | IsMIS x} = 1) := by
    have hsub : {x : ℤ → Fin 2 | IsWeakTwoColoring x} ⊆ misFromWeak ⁻¹' {x : ℤ → Fin 2 | IsMIS x} := by
      intro x hx
      exact misFromWeak_isMIS_of_isWeak x hx
    have hpre :
        (μ : Measure (ℤ → Fin 2)) (misFromWeak ⁻¹' {x : ℤ → Fin 2 | IsMIS x}) = 1 := by
      have hle :
          (μ : Measure (ℤ → Fin 2)) {x : ℤ → Fin 2 | IsWeakTwoColoring x}
            ≤ (μ : Measure (ℤ → Fin 2)) (misFromWeak ⁻¹' {x : ℤ → Fin 2 | IsMIS x}) :=
        measure_mono hsub
      have hle1 :
          (μ : Measure (ℤ → Fin 2)) (misFromWeak ⁻¹' {x : ℤ → Fin 2 | IsMIS x}) ≤ 1 := by
        have : (μ : Measure (ℤ → Fin 2)) (misFromWeak ⁻¹' {x : ℤ → Fin 2 | IsMIS x})
            ≤ (μ : Measure (ℤ → Fin 2)) Set.univ := measure_mono (subset_univ _)
        simpa using this
      have hge : (1 : ENNReal) ≤
          (μ : Measure (ℤ → Fin 2)) (misFromWeak ⁻¹' {x : ℤ → Fin 2 | IsMIS x}) := by
        simpa [hweak] using hle
      exact le_antisymm hle1 hge
    have hmap :
        (μMIS : Measure (ℤ → Fin 2)) {x : ℤ → Fin 2 | IsMIS x}
          = (μ : Measure (ℤ → Fin 2)) (misFromWeak ⁻¹' {x : ℤ → Fin 2 | IsMIS x}) := by
      simpa [μMIS] using
        (ProbabilityMeasure.map_apply' μ measurable_misFromWeak.aemeasurable
          FiniteDependence.measurableSet_isMIS)
    exact hmap.trans hpre
  have hexMIS5 : ExistsStationaryKDependentMIS 5 := by
    refine ⟨μMIS, ?_⟩
    exact ⟨hstatMIS, hdepMIS, hMISsupport⟩
  exact LowerBoundBridge.not_exists_stationary_fiveDependent_MIS hexMIS5

/--
No stationary `1`-dependent proper `3`-coloring exists on `ℤ`.

Proof idea: the ascent factor `Y_i = 1{C_i < C_{i+1}}` turns such a process into a stationary
`2`-dependent weak-2-coloring, contradicting
`not_exists_stationary_twoDependent_weakTwoColoring`.
-/
theorem not_exists_stationary_oneDependent_threeColoring :
    ¬ ∃ μ : ProbabilityMeasure (ℤ → Fin 3),
        IsStationary μ ∧
        IsKDependentCut μ 1 ∧
        (μ : Measure (ℤ → Fin 3)) {x | IsColoring (q := 3) x} = 1 := by
  intro h
  rcases h with ⟨μ3, hstat3, hdep1, hcol3⟩
  let μ2 : ProbabilityMeasure (ℤ → Fin 2) := μ3.map measurable_weakTwoFromThree.aemeasurable

  have hdep1' : FiniteDependence.Coloring.IsKDependent (q := 3) μ3 1 := by
    simpa [IsKDependentCut, FiniteDependence.Coloring.IsKDependent] using hdep1

  have hstat2 : IsStationary μ2 := by
    have hcomm :
        (FiniteDependence.Coloring.shift (q := 2)) ∘ weakTwoFromThree
          = weakTwoFromThree ∘ (FiniteDependence.Coloring.shift (q := 3)) := by
      funext c
      simpa [Function.comp] using (weakTwoFromThree_shift c).symm
    have hstat3' : FiniteDependence.Coloring.IsStationary (q := 3) μ3 := by
      simpa [IsStationary, FiniteDependence.Coloring.IsStationary] using hstat3
    simpa [μ2, IsStationary, FiniteDependence.Coloring.IsStationary] using
      (FiniteDependence.Coloring.isStationary_map_of_comm
        (hf := measurable_weakTwoFromThree)
        (hcomm := hcomm) (hstat := hstat3'))

  have hdep2 : IsKDependentCut μ2 2 := by
    have hkdepMap : FiniteDependence.Coloring.IsKDependent (q := 2) μ2 2 :=
      FiniteDependence.Coloring.isKDependent_map_of_past_future
        (hf := measurable_weakTwoFromThree.aemeasurable) (hdep := hdep1')
        (cut := fun i => i + 1) (hpast := comap_past_le_weak)
        (hfuture := comap_future_le_weak_k2)
    simpa [IsKDependentCut, FiniteDependence.Coloring.IsKDependent] using hkdepMap

  have hweak2 :
      ((μ2 : Measure (ℤ → Fin 2)) {x : ℤ → Fin 2 | IsWeakTwoColoring x} = 1) := by
    have hpre :
        (μ3 : Measure (ℤ → Fin 3)) (weakTwoFromThree ⁻¹' {x : ℤ → Fin 2 | IsWeakTwoColoring x}) = 1 := by
      have hsub :
          {c : ℤ → Fin 3 | IsColoring (q := 3) c}
            ⊆ weakTwoFromThree ⁻¹' {x : ℤ → Fin 2 | IsWeakTwoColoring x} := by
        intro c hc
        exact weakTwoFromThree_isWeak_of_isColoring c hc
      have hle :
          (μ3 : Measure (ℤ → Fin 3)) {c : ℤ → Fin 3 | IsColoring (q := 3) c}
            ≤ (μ3 : Measure (ℤ → Fin 3))
                (weakTwoFromThree ⁻¹' {x : ℤ → Fin 2 | IsWeakTwoColoring x}) :=
        measure_mono hsub
      have hle1 :
          (μ3 : Measure (ℤ → Fin 3)) (weakTwoFromThree ⁻¹' {x : ℤ → Fin 2 | IsWeakTwoColoring x}) ≤ 1 := by
        have : (μ3 : Measure (ℤ → Fin 3))
            (weakTwoFromThree ⁻¹' {x : ℤ → Fin 2 | IsWeakTwoColoring x})
              ≤ (μ3 : Measure (ℤ → Fin 3)) Set.univ := measure_mono (subset_univ _)
        simpa using this
      have hge : (1 : ENNReal) ≤
          (μ3 : Measure (ℤ → Fin 3)) (weakTwoFromThree ⁻¹' {x : ℤ → Fin 2 | IsWeakTwoColoring x}) := by
        simpa [hcol3] using hle
      exact le_antisymm hle1 hge
    have hmap :
        (μ2 : Measure (ℤ → Fin 2)) {x : ℤ → Fin 2 | IsWeakTwoColoring x}
          = (μ3 : Measure (ℤ → Fin 3)) (weakTwoFromThree ⁻¹' {x : ℤ → Fin 2 | IsWeakTwoColoring x}) := by
      simpa [μ2] using
        (ProbabilityMeasure.map_apply' μ3 measurable_weakTwoFromThree.aemeasurable
          FiniteDependence.measurableSet_isWeakTwoColoring)
    exact hmap.trans hpre

  have hexWeak2 : ExistsStationaryKDependentWeakTwoColoring 2 := by
    refine ⟨μ2, ?_⟩
    exact ⟨hstat2, hdep2, hweak2⟩

  exact not_exists_stationary_twoDependent_weakTwoColoring hexWeak2

end WeakTwo

end FiniteDependence
