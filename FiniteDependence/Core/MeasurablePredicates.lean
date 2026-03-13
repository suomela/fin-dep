import FiniteDependence.API.Definitions

import Mathlib.MeasureTheory.Measure.Map
import Mathlib.MeasureTheory.MeasurableSpace.Prod

/-!
# Measurability of binary SFT predicates on `ℤ`

Shared measurable-set lemmas for the standard predicates from
`FiniteDependence/API/Definitions.lean`.
-/

namespace FiniteDependence

open MeasureTheory

private lemma measurable_eq_const {q : ℕ} (i : ℤ) (a : Fin q) :
    Measurable fun x : ℤ → Fin q => x i = a := by
  have hi : Measurable (fun x : ℤ → Fin q => x i) := by
    simpa using (measurable_pi_apply (a := i))
  exact hi.eq_const a

private lemma measurable_eq_sites {q : ℕ} (i j : ℤ) :
    Measurable fun x : ℤ → Fin q => x i = x j := by
  have hi : Measurable (fun x : ℤ → Fin q => x i) := by
    simpa using (measurable_pi_apply (a := i))
  have hj : Measurable (fun x : ℤ → Fin q => x j) := by
    simpa using (measurable_pi_apply (a := j))
  exact hi.eq hj

lemma measurable_no11 : Measurable fun x : ℤ → Fin 2 => No11 x := by
  refine Measurable.forall fun i => ?_
  exact ((measurable_eq_const i (1 : Fin 2)).and
    (measurable_eq_const (i + 1) (1 : Fin 2))).not

lemma measurableSet_no11 : MeasurableSet {x : ℤ → Fin 2 | No11 x} :=
  measurable_no11.setOf

lemma measurable_no000 : Measurable fun x : ℤ → Fin 2 => No000 x := by
  refine Measurable.forall fun i => ?_
  exact ((measurable_eq_const i (0 : Fin 2)).and
    ((measurable_eq_const (i + 1) (0 : Fin 2)).and
      (measurable_eq_const (i + 2) (0 : Fin 2)))).not

lemma measurableSet_no000 : MeasurableSet {x : ℤ → Fin 2 | No000 x} :=
  measurable_no000.setOf

lemma measurable_no111 : Measurable fun x : ℤ → Fin 2 => No111 x := by
  refine Measurable.forall fun i => ?_
  exact ((measurable_eq_const i (1 : Fin 2)).and
    ((measurable_eq_const (i + 1) (1 : Fin 2)).and
      (measurable_eq_const (i + 2) (1 : Fin 2)))).not

lemma measurableSet_no111 : MeasurableSet {x : ℤ → Fin 2 | No111 x} :=
  measurable_no111.setOf

lemma measurable_isMIS : Measurable fun x : ℤ → Fin 2 => IsMIS x :=
  measurable_no11.and measurable_no000

lemma measurableSet_isMIS : MeasurableSet {x : ℤ → Fin 2 | IsMIS x} :=
  measurable_isMIS.setOf

lemma measurable_isWeakTwoColoring : Measurable fun x : ℤ → Fin 2 => IsWeakTwoColoring x :=
  measurable_no000.and measurable_no111

lemma measurableSet_isWeakTwoColoring : MeasurableSet {x : ℤ → Fin 2 | IsWeakTwoColoring x} :=
  measurable_isWeakTwoColoring.setOf

lemma measurable_isColoring (q : ℕ) : Measurable fun x : ℤ → Fin q => IsColoring x := by
  refine Measurable.forall fun i => ?_
  exact (measurable_eq_sites (q := q) i (i + 1)).not

lemma measurableSet_isColoring (q : ℕ) :
    MeasurableSet ({x : ℤ → Fin q | IsColoring x} : Set (ℤ → Fin q)) :=
  (measurable_isColoring q).setOf

private lemma measurable_hasNeighbor (a b : Fin 3) (i : ℤ) :
    Measurable fun x : ℤ → Fin 3 => x i = a → x (i - 1) = b ∨ x (i + 1) = b :=
  (measurable_eq_const (q := 3) i a).imp
    ((measurable_eq_const (q := 3) (i - 1) b).or
      (measurable_eq_const (q := 3) (i + 1) b))

private lemma measurable_hasZeroAndOneNeighbor (i : ℤ) :
    Measurable fun x : ℤ → Fin 3 =>
      x i = 2 →
        (x (i - 1) = 0 ∨ x (i + 1) = 0) ∧
          (x (i - 1) = 1 ∨ x (i + 1) = 1) :=
  (measurable_eq_const (q := 3) i (2 : Fin 3)).imp
    (((measurable_eq_const (q := 3) (i - 1) (0 : Fin 3)).or
        (measurable_eq_const (q := 3) (i + 1) (0 : Fin 3))).and
      ((measurable_eq_const (q := 3) (i - 1) (1 : Fin 3)).or
        (measurable_eq_const (q := 3) (i + 1) (1 : Fin 3))))

lemma measurable_isGreedyThreeColoring :
    Measurable fun x : ℤ → Fin 3 => IsGreedyThreeColoring x := by
  have h1 :
      Measurable fun x : ℤ → Fin 3 =>
        ∀ i : ℤ, x i = 1 → x (i - 1) = 0 ∨ x (i + 1) = 0 :=
    Measurable.forall fun i => measurable_hasNeighbor (a := 1) (b := 0) i
  have h2 :
      Measurable fun x : ℤ → Fin 3 =>
        ∀ i : ℤ, x i = 2 →
          (x (i - 1) = 0 ∨ x (i + 1) = 0) ∧
            (x (i - 1) = 1 ∨ x (i + 1) = 1) :=
    Measurable.forall measurable_hasZeroAndOneNeighbor
  simpa [IsGreedyThreeColoring] using (measurable_isColoring 3).and (h1.and h2)

lemma measurableSet_isGreedyThreeColoring :
    MeasurableSet ({x : ℤ → Fin 3 | IsGreedyThreeColoring x} : Set (ℤ → Fin 3)) :=
  measurable_isGreedyThreeColoring.setOf

end FiniteDependence
