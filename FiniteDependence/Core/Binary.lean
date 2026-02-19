import FiniteDependence.Core.Process

import Mathlib.MeasureTheory.MeasurableSpace.Pi

/-!
# Binary adapters (`Fin 2` ↔ `Bool`)

Shared conversion helpers for binary processes on `ℤ`.

This module centralizes the basic map from `Fin 2`-valued configurations to `Bool`-valued
configurations used by bridge proofs.
-/

namespace FiniteDependence

open MeasureTheory

/-- Canonical conversion from `Fin 2` to `Bool` (`0 ↦ false`, `1 ↦ true`). -/
def fin2ToBool (a : Fin 2) : Bool :=
  decide (a = (1 : Fin 2))

/-- Canonical conversion from `Bool` to `Fin 2` (`false ↦ 0`, `true ↦ 1`). -/
def boolToFin2 (b : Bool) : Fin 2 :=
  if b then 1 else 0

@[simp] lemma boolToFin2_false : boolToFin2 false = (0 : Fin 2) := by
  simp [boolToFin2]

@[simp] lemma boolToFin2_true : boolToFin2 true = (1 : Fin 2) := by
  simp [boolToFin2]

lemma fin2ToBool_eq_true_iff (a : Fin 2) : fin2ToBool a = true ↔ a = (1 : Fin 2) := by
  simp [fin2ToBool]

lemma fin2ToBool_eq_false_iff (a : Fin 2) : fin2ToBool a = false ↔ a = (0 : Fin 2) := by
  fin_cases a <;> simp [fin2ToBool]

@[simp] lemma fin2ToBool_boolToFin2 (b : Bool) : fin2ToBool (boolToFin2 b) = b := by
  cases b <;> simp [boolToFin2, fin2ToBool]

@[simp] lemma boolToFin2_fin2ToBool (a : Fin 2) : boolToFin2 (fin2ToBool a) = a := by
  fin_cases a <;> simp [boolToFin2, fin2ToBool]

lemma measurable_fin2ToBool : Measurable fin2ToBool := by
  classical
  simpa [fin2ToBool] using
    (Measurable.of_discrete : Measurable (fun a : Fin 2 => decide (a = (1 : Fin 2))))

lemma measurable_boolToFin2 : Measurable boolToFin2 := by
  classical
  simpa [boolToFin2] using
    (Measurable.of_discrete : Measurable (fun b : Bool => if b then (1 : Fin 2) else 0))

/-- Pointwise conversion of a `Fin 2`-valued configuration into a `Bool`-valued one. -/
def toBoolConfig (x : ℤ → Fin 2) : ℤ → Bool :=
  fun i => fin2ToBool (x i)

/-- Pointwise conversion of a `Bool`-valued configuration into a `Fin 2`-valued one. -/
def toFin2Config (x : ℤ → Bool) : ℤ → Fin 2 :=
  fun i => boolToFin2 (x i)

lemma measurable_toBoolConfig : Measurable toBoolConfig := by
  classical
  refine measurable_pi_lambda _ (fun i => ?_)
  simpa [toBoolConfig] using measurable_fin2ToBool.comp (measurable_pi_apply (a := i))

lemma measurable_toFin2Config : Measurable toFin2Config := by
  classical
  refine measurable_pi_lambda _ (fun i => ?_)
  simpa [toFin2Config] using measurable_boolToFin2.comp (measurable_pi_apply (a := i))

lemma aemeasurable_toBoolConfig (μ : ProbabilityMeasure (ℤ → Fin 2)) :
    AEMeasurable toBoolConfig (μ : Measure (ℤ → Fin 2)) :=
  measurable_toBoolConfig.aemeasurable

lemma toBoolConfig_eq_true_iff (x : ℤ → Fin 2) (i : ℤ) :
    toBoolConfig x i = true ↔ x i = (1 : Fin 2) := by
  simpa [toBoolConfig] using fin2ToBool_eq_true_iff (a := x i)

lemma toBoolConfig_eq_false_iff (x : ℤ → Fin 2) (i : ℤ) :
    toBoolConfig x i = false ↔ x i = (0 : Fin 2) := by
  simpa [toBoolConfig] using fin2ToBool_eq_false_iff (a := x i)

lemma toBoolConfig_shift (x : ℤ → Fin 2) :
    toBoolConfig (shift x) = shift (toBoolConfig x) := by
  ext i
  simp [toBoolConfig, shift, FiniteDependence.shift, add_assoc]

end FiniteDependence
