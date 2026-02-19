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

lemma measurableSet_no11 : MeasurableSet {x : ℤ → Fin 2 | No11 x} := by
  classical
  have hsingle (i : ℤ) : MeasurableSet {x : ℤ → Fin 2 | x i = 1 ∧ x (i + 1) = 1} := by
    have hmeas :
        Measurable fun x : ℤ → Fin 2 => (x i, x (i + 1)) :=
      (measurable_pi_apply (a := i)).prodMk (measurable_pi_apply (a := i + 1))
    simpa [Set.preimage, Set.mem_singleton_iff] using
      (measurableSet_singleton ((1 : Fin 2), (1 : Fin 2))).preimage hmeas
  have hcomp (i : ℤ) : MeasurableSet {x : ℤ → Fin 2 | ¬(x i = 1 ∧ x (i + 1) = 1)} :=
    (hsingle i).compl
  have hEq :
      ({x : ℤ → Fin 2 | No11 x}
        = ⋂ i : ℤ, {x : ℤ → Fin 2 | ¬(x i = 1 ∧ x (i + 1) = 1)}) := by
    ext x
    simp [No11]
  simpa [hEq] using MeasurableSet.iInter hcomp

lemma measurableSet_no000 : MeasurableSet {x : ℤ → Fin 2 | No000 x} := by
  classical
  have hsingle (i : ℤ) :
      MeasurableSet {x : ℤ → Fin 2 | x i = 0 ∧ x (i + 1) = 0 ∧ x (i + 2) = 0} := by
    have hmeas :
        Measurable fun x : ℤ → Fin 2 => (x i, x (i + 1), x (i + 2)) :=
      (measurable_pi_apply (a := i)).prodMk
        ((measurable_pi_apply (a := i + 1)).prodMk (measurable_pi_apply (a := i + 2)))
    simpa [Set.preimage, Set.mem_singleton_iff, and_assoc] using
      (measurableSet_singleton ((0 : Fin 2), (0 : Fin 2), (0 : Fin 2))).preimage hmeas
  have hcomp (i : ℤ) :
      MeasurableSet {x : ℤ → Fin 2 | ¬(x i = 0 ∧ x (i + 1) = 0 ∧ x (i + 2) = 0)} :=
    (hsingle i).compl
  have hEq :
      ({x : ℤ → Fin 2 | No000 x}
        = ⋂ i : ℤ, {x : ℤ → Fin 2 | ¬(x i = 0 ∧ x (i + 1) = 0 ∧ x (i + 2) = 0)}) := by
    ext x
    simp [No000]
  simpa [hEq] using MeasurableSet.iInter hcomp

lemma measurableSet_no111 : MeasurableSet {x : ℤ → Fin 2 | No111 x} := by
  classical
  have hsingle (i : ℤ) :
      MeasurableSet {x : ℤ → Fin 2 | x i = 1 ∧ x (i + 1) = 1 ∧ x (i + 2) = 1} := by
    have hmeas :
        Measurable fun x : ℤ → Fin 2 => (x i, x (i + 1), x (i + 2)) :=
      (measurable_pi_apply (a := i)).prodMk
        ((measurable_pi_apply (a := i + 1)).prodMk (measurable_pi_apply (a := i + 2)))
    simpa [Set.preimage, Set.mem_singleton_iff, and_assoc] using
      (measurableSet_singleton ((1 : Fin 2), (1 : Fin 2), (1 : Fin 2))).preimage hmeas
  have hcomp (i : ℤ) :
      MeasurableSet {x : ℤ → Fin 2 | ¬(x i = 1 ∧ x (i + 1) = 1 ∧ x (i + 2) = 1)} :=
    (hsingle i).compl
  have hEq :
      ({x : ℤ → Fin 2 | No111 x}
        = ⋂ i : ℤ, {x : ℤ → Fin 2 | ¬(x i = 1 ∧ x (i + 1) = 1 ∧ x (i + 2) = 1)}) := by
    ext x
    simp [No111]
  simpa [hEq] using MeasurableSet.iInter hcomp

lemma measurableSet_isMIS : MeasurableSet {x : ℤ → Fin 2 | IsMIS x} := by
  classical
  have hEq :
      ({x : ℤ → Fin 2 | IsMIS x} = {x : ℤ → Fin 2 | No11 x} ∩ {x : ℤ → Fin 2 | No000 x}) := by
    ext x
    simp [IsMIS]
  simpa [hEq] using measurableSet_no11.inter measurableSet_no000

lemma measurableSet_isWeakTwoColoring : MeasurableSet {x : ℤ → Fin 2 | IsWeakTwoColoring x} := by
  classical
  have hEq :
      ({x : ℤ → Fin 2 | IsWeakTwoColoring x}
        = {x : ℤ → Fin 2 | No000 x} ∩ {x : ℤ → Fin 2 | No111 x}) := by
    ext x
    simp [IsWeakTwoColoring]
  simpa [hEq] using measurableSet_no000.inter measurableSet_no111

private lemma measurableSet_isColoring3 : MeasurableSet ({x : ℤ → Fin 3 | IsColoring x} : Set (ℤ → Fin 3)) := by
  classical
  have hbad (i : ℤ) : MeasurableSet ({x : ℤ → Fin 3 | x i = x (i + 1)} : Set (ℤ → Fin 3)) := by
    have hsingle (a : Fin 3) :
        MeasurableSet ({x : ℤ → Fin 3 | x i = a ∧ x (i + 1) = a} : Set (ℤ → Fin 3)) := by
      have hmeas : Measurable (fun x : ℤ → Fin 3 => (x i, x (i + 1))) :=
        (measurable_pi_apply (a := i)).prodMk (measurable_pi_apply (a := i + 1))
      simpa [Set.preimage, Set.mem_singleton_iff] using
        (measurableSet_singleton (a, a)).preimage hmeas
    have hEq :
        ({x : ℤ → Fin 3 | x i = x (i + 1)} : Set (ℤ → Fin 3))
          = ⋃ a : Fin 3, ({x : ℤ → Fin 3 | x i = a ∧ x (i + 1) = a} : Set (ℤ → Fin 3)) := by
      ext x
      constructor
      · intro hx
        refine Set.mem_iUnion.2 ?_
        refine ⟨x i, ?_⟩
        constructor
        · rfl
        · exact hx.symm
      · intro hx
        rcases Set.mem_iUnion.1 hx with ⟨a, ha⟩
        exact ha.1.trans ha.2.symm
    simpa [hEq] using MeasurableSet.iUnion hsingle
  have hEq :
      ({x : ℤ → Fin 3 | IsColoring x} : Set (ℤ → Fin 3))
        = (⋃ i : ℤ, ({x : ℤ → Fin 3 | x i = x (i + 1)} : Set (ℤ → Fin 3)))ᶜ := by
    ext x
    simp [IsColoring]
  simpa [hEq] using (MeasurableSet.iUnion hbad).compl

lemma measurableSet_isGreedyThreeColoring :
    MeasurableSet ({x : ℤ → Fin 3 | IsGreedyThreeColoring x} : Set (ℤ → Fin 3)) := by
  classical
  have hImpNeighbor (a b : Fin 3) (i : ℤ) :
      MeasurableSet ({x : ℤ → Fin 3 | x i = a → x (i - 1) = b ∨ x (i + 1) = b} : Set (ℤ → Fin 3)) := by
    let A : Set (ℤ → Fin 3) := {x : ℤ → Fin 3 | x i = a}
    let B : Set (ℤ → Fin 3) := {x : ℤ → Fin 3 | x (i - 1) = b}
    let C : Set (ℤ → Fin 3) := {x : ℤ → Fin 3 | x (i + 1) = b}
    have hAi : Measurable (fun x : ℤ → Fin 3 => x i) := by
      simpa using (measurable_pi_apply (a := i))
    have hBi : Measurable (fun x : ℤ → Fin 3 => x (i - 1)) := by
      simpa using (measurable_pi_apply (a := i - 1))
    have hCi : Measurable (fun x : ℤ → Fin 3 => x (i + 1)) := by
      simpa using (measurable_pi_apply (a := i + 1))
    have hA : MeasurableSet A := by
      simpa [A, Set.preimage, Set.mem_singleton_iff] using
        (measurableSet_singleton a).preimage hAi
    have hB : MeasurableSet B := by
      simpa [B, Set.preimage, Set.mem_singleton_iff] using
        (measurableSet_singleton b).preimage hBi
    have hC : MeasurableSet C := by
      simpa [C, Set.preimage, Set.mem_singleton_iff] using
        (measurableSet_singleton b).preimage hCi
    have hEq :
        ({x : ℤ → Fin 3 | x i = a → x (i - 1) = b ∨ x (i + 1) = b} : Set (ℤ → Fin 3))
          = Aᶜ ∪ (B ∪ C) := by
      ext x
      by_cases hxi : x i = a <;> simp [A, B, C, hxi, or_assoc]
    simpa [hEq, Set.union_assoc] using hA.compl.union (hB.union hC)

  have hcond1 (i : ℤ) :
      MeasurableSet ({x : ℤ → Fin 3 | x i = 1 → x (i - 1) = 0 ∨ x (i + 1) = 0} : Set (ℤ → Fin 3)) :=
    hImpNeighbor 1 0 i

  have hcond20 (i : ℤ) :
      MeasurableSet ({x : ℤ → Fin 3 | x i = 2 → x (i - 1) = 0 ∨ x (i + 1) = 0} : Set (ℤ → Fin 3)) :=
    hImpNeighbor 2 0 i

  have hcond21 (i : ℤ) :
      MeasurableSet ({x : ℤ → Fin 3 | x i = 2 → x (i - 1) = 1 ∨ x (i + 1) = 1} : Set (ℤ → Fin 3)) :=
    hImpNeighbor 2 1 i

  have hcond2 (i : ℤ) :
      MeasurableSet
        ({x : ℤ → Fin 3 | x i = 2 →
            (x (i - 1) = 0 ∨ x (i + 1) = 0) ∧
              (x (i - 1) = 1 ∨ x (i + 1) = 1)} : Set (ℤ → Fin 3)) := by
    let S0 : Set (ℤ → Fin 3) := {x : ℤ → Fin 3 | x i = 2 → x (i - 1) = 0 ∨ x (i + 1) = 0}
    let S1 : Set (ℤ → Fin 3) := {x : ℤ → Fin 3 | x i = 2 → x (i - 1) = 1 ∨ x (i + 1) = 1}
    have hS0 : MeasurableSet S0 := by simpa [S0] using hcond20 i
    have hS1 : MeasurableSet S1 := by simpa [S1] using hcond21 i
    have hEq :
        ({x : ℤ → Fin 3 | x i = 2 →
            (x (i - 1) = 0 ∨ x (i + 1) = 0) ∧
              (x (i - 1) = 1 ∨ x (i + 1) = 1)} : Set (ℤ → Fin 3))
          = S0 ∩ S1 := by
      ext x
      constructor
      · intro hx
        refine ⟨?_, ?_⟩
        · intro hi
          exact (hx hi).1
        · intro hi
          exact (hx hi).2
      · intro hx hi
        exact ⟨hx.1 hi, hx.2 hi⟩
    simpa [hEq] using hS0.inter hS1

  have hcond1All :
      MeasurableSet
        ({x : ℤ → Fin 3 | ∀ i : ℤ, x i = 1 → x (i - 1) = 0 ∨ x (i + 1) = 0} : Set (ℤ → Fin 3)) := by
    have hEq :
        ({x : ℤ → Fin 3 | ∀ i : ℤ, x i = 1 → x (i - 1) = 0 ∨ x (i + 1) = 0} : Set (ℤ → Fin 3))
          = ⋂ i : ℤ, ({x : ℤ → Fin 3 | x i = 1 → x (i - 1) = 0 ∨ x (i + 1) = 0} : Set (ℤ → Fin 3)) := by
      ext x
      simp
    simpa [hEq] using MeasurableSet.iInter hcond1

  have hcond2All :
      MeasurableSet
        ({x : ℤ → Fin 3 | ∀ i : ℤ, x i = 2 →
            (x (i - 1) = 0 ∨ x (i + 1) = 0) ∧
              (x (i - 1) = 1 ∨ x (i + 1) = 1)} : Set (ℤ → Fin 3)) := by
    have hEq :
        ({x : ℤ → Fin 3 | ∀ i : ℤ, x i = 2 →
            (x (i - 1) = 0 ∨ x (i + 1) = 0) ∧
              (x (i - 1) = 1 ∨ x (i + 1) = 1)} : Set (ℤ → Fin 3))
          = ⋂ i : ℤ,
              ({x : ℤ → Fin 3 | x i = 2 →
                  (x (i - 1) = 0 ∨ x (i + 1) = 0) ∧
                    (x (i - 1) = 1 ∨ x (i + 1) = 1)} : Set (ℤ → Fin 3)) := by
      ext x
      simp
    simpa [hEq] using MeasurableSet.iInter hcond2

  have hEq :
      ({x : ℤ → Fin 3 | IsGreedyThreeColoring x} : Set (ℤ → Fin 3))
        =
          ({x : ℤ → Fin 3 | IsColoring x} : Set (ℤ → Fin 3)) ∩
            (({x : ℤ → Fin 3 | ∀ i : ℤ, x i = 1 → x (i - 1) = 0 ∨ x (i + 1) = 0} :
              Set (ℤ → Fin 3)) ∩
              ({x : ℤ → Fin 3 | ∀ i : ℤ, x i = 2 →
                  (x (i - 1) = 0 ∨ x (i + 1) = 0) ∧
                    (x (i - 1) = 1 ∨ x (i + 1) = 1)} : Set (ℤ → Fin 3))) := by
    ext x
    simp [IsGreedyThreeColoring, and_assoc]

  rw [hEq]
  exact measurableSet_isColoring3.inter (hcond1All.inter hcond2All)

end FiniteDependence
