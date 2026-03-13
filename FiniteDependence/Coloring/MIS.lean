import FiniteDependence.Coloring.Existence
import FiniteDependence.Coloring.MeasureHelpers
import FiniteDependence.API.Definitions
import FiniteDependence.Core.MeasurablePredicates
import Mathlib.MeasureTheory.Measure.Map
import Mathlib.MeasureTheory.MeasurableSpace.Prod
import Mathlib.Tactic

/-!
# Maximal independent sets (MIS) from the `2`-dependent `3`-coloring

As an application of Holroyd–Liggett, *Finitely dependent coloring* (arXiv:1403.2448v4), we
construct a stationary `6`-dependent `0/1` process on `ℤ` that is almost surely a maximal
independent set (MIS) for the integer line graph.

We view a `0/1` configuration as a set of occupied vertices (`1` means “in the MIS”).
Being a maximal independent set on the line is equivalent to forbidding the two finite patterns:

* `11` (adjacent ones) — independence;
* `000` (a run of three zeros) — maximality.

The construction is a greedy local algorithm (radius `2`) applied to the stationary `2`-dependent
`3`-coloring from Theorem 1: accept all vertices of color `0`, then accept vertices of color `1`
that do not touch an accepted vertex, and finally do the same for color `2`.

Main declarations:

* `FiniteDependence.Coloring.Model.greedyMIS` — the greedy local map `Fin 3` → `Fin 2`;
* `FiniteDependence.Coloring.exists_stationary_sixDependent_MIS` — existence of a stationary
  `6`-dependent MIS process on `ℤ`.
-/

open scoped BigOperators

namespace FiniteDependence.Coloring

open MeasureTheory ProbabilityTheory Set

/-! ## MIS as forbidden patterns -/

/-- No adjacent ones (`11`). -/
abbrev No11 (x : ℤ → Fin 2) : Prop :=
  FiniteDependence.No11 x

/-- No run of three zeros (`000`). -/
abbrev No000 (x : ℤ → Fin 2) : Prop :=
  FiniteDependence.No000 x

/-- A maximal independent set configuration on `ℤ`, phrased as forbidden patterns `11` and `000`. -/
abbrev IsMIS (x : ℤ → Fin 2) : Prop :=
  FiniteDependence.IsMIS x

/-! ## Greedy MIS map from `Fin 3` to `Fin 2` -/

namespace Model

/-- Greedy MIS map from a `3`-coloring, processing colors `0,1,2` in order. -/
def greedyMIS (c : ℤ → Fin 3) : ℤ → Fin 2 :=
  fun i =>
    if c i = 0 then
      1
    else if c i = 1 then
      if c (i - 1) = 0 ∨ c (i + 1) = 0 then 0 else 1
    else
      if c (i - 1) = 0 ∨ c (i + 1) = 0 then 0
      else if
          (c (i - 1) = 1 ∧ c (i - 2) ≠ 0) ∨ (c (i + 1) = 1 ∧ c (i + 2) ≠ 0) then
        0
      else
        1

/-! ### Measurability -/

private lemma measurable_greedyMIS_at {m : MeasurableSpace (ℤ → Fin 3)} (i : ℤ)
    (hm2 : Measurable[m] fun c : ℤ → Fin 3 => c (i - 2))
    (hm1 : Measurable[m] fun c : ℤ → Fin 3 => c (i - 1))
    (h0 : Measurable[m] fun c : ℤ → Fin 3 => c i)
    (hp1 : Measurable[m] fun c : ℤ → Fin 3 => c (i + 1))
    (hp2 : Measurable[m] fun c : ℤ → Fin 3 => c (i + 2)) :
    Measurable[m] fun c : ℤ → Fin 3 => greedyMIS c i := by
  classical
  letI : MeasurableSpace (ℤ → Fin 3) := m

  have h0set : MeasurableSet {c : ℤ → Fin 3 | c i = (0 : Fin 3)} := by
    simpa [Set.preimage, Set.mem_singleton_iff] using
      (measurableSet_singleton (0 : Fin 3)).preimage h0
  have h1set : MeasurableSet {c : ℤ → Fin 3 | c i = (1 : Fin 3)} := by
    simpa [Set.preimage, Set.mem_singleton_iff] using
      (measurableSet_singleton (1 : Fin 3)).preimage h0

  have hleft0 : MeasurableSet {c : ℤ → Fin 3 | c (i - 1) = (0 : Fin 3)} := by
    simpa [Set.preimage, Set.mem_singleton_iff] using
      (measurableSet_singleton (0 : Fin 3)).preimage hm1
  have hright0 : MeasurableSet {c : ℤ → Fin 3 | c (i + 1) = (0 : Fin 3)} := by
    simpa [Set.preimage, Set.mem_singleton_iff] using
      (measurableSet_singleton (0 : Fin 3)).preimage hp1
  have hconf0 : MeasurableSet {c : ℤ → Fin 3 | c (i - 1) = 0 ∨ c (i + 1) = 0} :=
    hleft0.union hright0

  have hleft1 : MeasurableSet {c : ℤ → Fin 3 | c (i - 1) = (1 : Fin 3)} := by
    simpa [Set.preimage, Set.mem_singleton_iff] using
      (measurableSet_singleton (1 : Fin 3)).preimage hm1
  have hright1 : MeasurableSet {c : ℤ → Fin 3 | c (i + 1) = (1 : Fin 3)} := by
    simpa [Set.preimage, Set.mem_singleton_iff] using
      (measurableSet_singleton (1 : Fin 3)).preimage hp1

  have hleft2_0 : MeasurableSet {c : ℤ → Fin 3 | c (i - 2) = (0 : Fin 3)} := by
    simpa [Set.preimage, Set.mem_singleton_iff] using
      (measurableSet_singleton (0 : Fin 3)).preimage hm2
  have hright2_0 : MeasurableSet {c : ℤ → Fin 3 | c (i + 2) = (0 : Fin 3)} := by
    simpa [Set.preimage, Set.mem_singleton_iff] using
      (measurableSet_singleton (0 : Fin 3)).preimage hp2

  have hleft2_ne0 : MeasurableSet {c : ℤ → Fin 3 | c (i - 2) ≠ (0 : Fin 3)} := hleft2_0.compl
  have hright2_ne0 : MeasurableSet {c : ℤ → Fin 3 | c (i + 2) ≠ (0 : Fin 3)} := hright2_0.compl

  have hconf1_left : MeasurableSet {c : ℤ → Fin 3 | c (i - 1) = 1 ∧ c (i - 2) ≠ 0} :=
    hleft1.inter hleft2_ne0
  have hconf1_right : MeasurableSet {c : ℤ → Fin 3 | c (i + 1) = 1 ∧ c (i + 2) ≠ 0} :=
    hright1.inter hright2_ne0
  have hconf1 :
      MeasurableSet
        {c : ℤ → Fin 3 |
          (c (i - 1) = 1 ∧ c (i - 2) ≠ 0) ∨ (c (i + 1) = 1 ∧ c (i + 2) ≠ 0)} :=
    hconf1_left.union hconf1_right

  -- Assemble measurability by nested `ite`. Branches are constant, hence measurable.
  refine Measurable.ite h0set measurable_const ?_
  refine Measurable.ite h1set ?_ ?_
  · refine Measurable.ite hconf0 measurable_const measurable_const
  · refine Measurable.ite hconf0 measurable_const ?_
    refine Measurable.ite hconf1 measurable_const measurable_const

lemma measurable_greedyMIS : Measurable greedyMIS := by
  classical
  refine measurable_pi_lambda _ (fun i => ?_)
  refine measurable_greedyMIS_at (m := inferInstance) (i := i)
    (hm2 := ?_) (hm1 := ?_) (h0 := ?_) (hp1 := ?_) (hp2 := ?_)
  · simpa using (measurable_pi_apply (a := i - 2))
  · simpa using (measurable_pi_apply (a := i - 1))
  · simpa using (measurable_pi_apply (a := i))
  · simpa using (measurable_pi_apply (a := i + 1))
  · simpa using (measurable_pi_apply (a := i + 2))

private def greedyMISOffsets : Fin 5 → ℤ
  | 0 => -2
  | 1 => -1
  | 2 => 0
  | 3 => 1
  | 4 => 2

private lemma measurable_greedyMIS_local {m : MeasurableSpace (ℤ → Fin 3)} (i : ℤ)
    (hcoords : ∀ t : Fin 5, Measurable[m] fun c : ℤ → Fin 3 => c (i + greedyMISOffsets t)) :
    Measurable[m] fun c : ℤ → Fin 3 => greedyMIS c i := by
  refine measurable_greedyMIS_at (m := m) (i := i)
    (hm2 := ?_) (hm1 := ?_) (h0 := ?_) (hp1 := ?_) (hp2 := ?_)
  · simpa [greedyMISOffsets] using hcoords 0
  · simpa [greedyMISOffsets] using hcoords 1
  · simpa [greedyMISOffsets] using hcoords 2
  · simpa [greedyMISOffsets] using hcoords 3
  · simpa [greedyMISOffsets] using hcoords 4

lemma greedyMIS_shift (c : ℤ → Fin 3) :
    greedyMIS (FiniteDependence.Coloring.shift (q := 3) c)
      = FiniteDependence.Coloring.shift (q := 2) (greedyMIS c) := by
  ext i
  simp [greedyMIS, FiniteDependence.Coloring.shift, FiniteDependence.shift, sub_eq_add_neg,
    add_assoc, add_left_comm, add_comm]

/-! ### Correctness on proper colorings -/

private lemma fin3_eq_two_of_ne_zero_of_ne_one (a : Fin 3) (h0 : a ≠ 0) (h1 : a ≠ 1) : a = 2 := by
  fin_cases a <;> simp at h0 h1 ⊢

private lemma fin3_eq_one_of_ne_zero_of_ne_two (a : Fin 3) (h0 : a ≠ 0) (h2 : a ≠ 2) : a = 1 := by
  fin_cases a <;> simp at h0 h2 ⊢

private lemma greedyMIS_adjacent (c : ℤ → Fin 3) (hc : IsColoring (q := 3) c) :
    ∀ i : ℤ, greedyMIS c i = 1 → greedyMIS c (i + 1) = 0 := by
  intro i hi
  by_cases hci0 : c i = 0
  · -- A color `0` vertex is always selected, so its right neighbor must be rejected.
    have hci1_ne0 : c (i + 1) ≠ 0 := by
      intro h
      exact (hc i) (by simpa [hci0] using h.symm)
    have hconf : c ((i + 1) - 1) = 0 ∨ c ((i + 1) + 1) = 0 := by
      left
      simpa using hci0
    unfold greedyMIS
    rw [if_neg hci1_ne0]
    by_cases hci1 : c (i + 1) = 1
    · rw [if_pos hci1]
      rw [if_pos hconf]
    · rw [if_neg hci1]
      rw [if_pos hconf]
  · by_cases hci1 : c i = 1
    · -- If a color `1` vertex is selected, then it has no adjacent color `0`,
      -- but it blocks any adjacent color `2`.
      have hconf_i : ¬(c (i - 1) = 0 ∨ c (i + 1) = 0) := by
        intro hconf
        have hgi0 : greedyMIS c i = 0 := by
          simp [greedyMIS, hci1, hconf]
        have h01 : (0 : Fin 2) ≠ 1 := by simp
        have hcontr : (0 : Fin 2) = 1 := by
          calc
            (0 : Fin 2) = greedyMIS c i := by symm; exact hgi0
            _ = 1 := hi
        exact h01 hcontr
      have hleft_ne0 : c (i - 1) ≠ 0 := by
        intro h
        exact hconf_i (Or.inl h)
      have hright_ne0 : c (i + 1) ≠ 0 := by
        intro h
        exact hconf_i (Or.inr h)
      have hright_ne1 : c (i + 1) ≠ 1 := by
        intro h
        exact (hc i) (by simpa [hci1] using h.symm)
      unfold greedyMIS
      rw [if_neg hright_ne0]
      rw [if_neg hright_ne1]
      by_cases hi2 : c (i + 2) = 0
      · have hP : c ((i + 1) - 1) = 0 ∨ c ((i + 1) + 1) = 0 := by
          right
          have hidx : i + 1 + 1 = i + 2 := by linarith
          simpa [hidx] using hi2
        rw [if_pos hP]
      · have hP : ¬(c ((i + 1) - 1) = 0 ∨ c ((i + 1) + 1) = 0) := by
          intro hP
          cases hP with
          | inl h =>
              exact hci0 (by simpa using h)
          | inr h =>
              have hidx : i + 1 + 1 = i + 2 := by linarith
              exact hi2 (by simpa [hidx] using h)
        rw [if_neg hP]
        have hQ :
            (c ((i + 1) - 1) = 1 ∧ c ((i + 1) - 2) ≠ 0) ∨
              (c ((i + 1) + 1) = 1 ∧ c ((i + 1) + 2) ≠ 0) := by
          left
          refine ⟨?_, ?_⟩
          · simpa using hci1
          · have hidx : i + 1 - 2 = i - 1 := by linarith
            simpa [hidx] using hleft_ne0
        rw [if_pos hQ]
    · -- `c i` is the remaining color `2`.
      have hci2 : c i = 2 := fin3_eq_two_of_ne_zero_of_ne_one (c i) hci0 hci1
      have hconf0_i : ¬(c (i - 1) = 0 ∨ c (i + 1) = 0) := by
        intro hconf
        have hgi0 : greedyMIS c i = 0 := by
          simp [greedyMIS, hci2, hconf]
        have h01 : (0 : Fin 2) ≠ 1 := by simp
        have hcontr : (0 : Fin 2) = 1 := by
          calc
            (0 : Fin 2) = greedyMIS c i := by symm; exact hgi0
            _ = 1 := hi
        exact h01 hcontr
      have hright_ne0 : c (i + 1) ≠ 0 := by
        intro h
        exact hconf0_i (Or.inr h)
      have hright_ne2 : c (i + 1) ≠ 2 := by
        intro h
        exact (hc i) (by simpa [hci2] using h.symm)
      have hright_eq1 : c (i + 1) = 1 :=
        fin3_eq_one_of_ne_zero_of_ne_two (c (i + 1)) hright_ne0 hright_ne2
      have hconf1_i :
          ¬((c (i - 1) = 1 ∧ c (i - 2) ≠ 0) ∨ (c (i + 1) = 1 ∧ c (i + 2) ≠ 0)) := by
        intro hconf
        have hgi0 : greedyMIS c i = 0 := by
          simp [greedyMIS, hci2, hconf0_i, hconf]
        have h01 : (0 : Fin 2) ≠ 1 := by simp
        have hcontr : (0 : Fin 2) = 1 := by
          calc
            (0 : Fin 2) = greedyMIS c i := by symm; exact hgi0
            _ = 1 := hi
        exact h01 hcontr
      have hi2_eq0 : c (i + 2) = 0 := by
        have : ¬(c (i + 2) ≠ 0) := by
          intro hne
          apply hconf1_i
          exact Or.inr ⟨hright_eq1, hne⟩
        exact not_ne_iff.mp this
      -- Now `i+1` has color `1` and a 0-neighbor at `i+2`, so it is rejected.
      have hci1_ne0 : c (i + 1) ≠ 0 := by
        simp [hright_eq1]
      unfold greedyMIS
      rw [if_neg hci1_ne0]
      rw [if_pos hright_eq1]
      have hP : c ((i + 1) - 1) = 0 ∨ c ((i + 1) + 1) = 0 := by
        right
        have hidx : i + 1 + 1 = i + 2 := by linarith
        simpa [hidx] using hi2_eq0
      rw [if_pos hP]

private lemma greedyMIS_zero_has_neighbor (c : ℤ → Fin 3) :
    ∀ i : ℤ, greedyMIS c i = 0 → greedyMIS c (i - 1) = 1 ∨ greedyMIS c (i + 1) = 1 := by
  intro i hi
  by_cases hci0 : c i = 0
  · simp [greedyMIS, hci0] at hi
  by_cases hci1 : c i = 1
  · have hconf : c (i - 1) = 0 ∨ c (i + 1) = 0 := by
      by_contra hconf
      have : greedyMIS c i = 1 := by
        simp [greedyMIS, hci1, hconf]
      have h01 : (0 : Fin 2) ≠ 1 := by simp
      have hcontr : (0 : Fin 2) = 1 := by
        calc
          (0 : Fin 2) = greedyMIS c i := by symm; exact hi
          _ = 1 := this
      exact h01 hcontr
    cases hconf with
    | inl hleft =>
        left
        simp [greedyMIS, hleft]
    | inr hright =>
        right
        simp [greedyMIS, hright]
  · by_cases hconf0 : c (i - 1) = 0 ∨ c (i + 1) = 0
    · cases hconf0 with
      | inl hleft =>
          left
          simp [greedyMIS, hleft]
      | inr hright =>
          right
          simp [greedyMIS, hright]
    · have hconf1 :
          (c (i - 1) = 1 ∧ c (i - 2) ≠ 0) ∨ (c (i + 1) = 1 ∧ c (i + 2) ≠ 0) := by
        by_contra hconf1
        have : greedyMIS c i = 1 := by
          simp [greedyMIS, hci0, hci1, hconf0, hconf1]
        have h01 : (0 : Fin 2) ≠ 1 := by simp
        have hcontr : (0 : Fin 2) = 1 := by
          calc
            (0 : Fin 2) = greedyMIS c i := by symm; exact hi
            _ = 1 := this
        exact h01 hcontr
      cases hconf1 with
      | inl hleft =>
          left
          have hidx2 : i - 1 - 1 = i - 2 := by linarith
          have hidx : i - 1 + 1 = i := by linarith
          have : greedyMIS c (i - 1) = 1 := by
            simp [greedyMIS, hleft.1, hleft.2, hci0, hidx, hidx2]
          exact this
      | inr hright =>
          right
          have hidx : i + 1 + 1 = i + 2 := by linarith
          have : greedyMIS c (i + 1) = 1 := by
            simp [greedyMIS, hright.1, hright.2, hci0, hidx]
          exact this

theorem greedyMIS_isMIS_of_isColoring (c : ℤ → Fin 3) (hc : IsColoring (q := 3) c) :
    IsMIS (greedyMIS c) := by
  refine ⟨?_, ?_⟩
  · intro i h
    have hzero : greedyMIS c (i + 1) = 0 := greedyMIS_adjacent c hc i h.1
    have h01 : (0 : Fin 2) ≠ 1 := by simp
    have hcontr : (0 : Fin 2) = 1 := by
      calc
        (0 : Fin 2) = greedyMIS c (i + 1) := by symm; exact hzero
        _ = 1 := h.2
    exact h01 hcontr
  · intro i h
    have hneigh := greedyMIS_zero_has_neighbor c (i + 1) h.2.1
    cases hneigh with
    | inl hl =>
        have hidx : i + 1 - 1 = i := by linarith
        have h01 : (0 : Fin 2) ≠ 1 := by simp
        have hcontr : (0 : Fin 2) = 1 := by
          calc
            (0 : Fin 2) = greedyMIS c i := by symm; exact h.1
            _ = 1 := by simpa [hidx] using hl
        exact h01 hcontr
    | inr hr =>
        have hidx : i + 1 + 1 = i + 2 := by linarith
        have h01 : (0 : Fin 2) ≠ 1 := by simp
        have hcontr : (0 : Fin 2) = 1 := by
          calc
            (0 : Fin 2) = greedyMIS c (i + 2) := by symm; exact h.2.2
            _ = 1 := by simpa [hidx] using hr
        exact h01 hcontr

/-! ### Locality (radius `2`) and `6`-dependence -/

private lemma comap_past_le (i : ℤ) :
    (pastMeasurableSpace (q := 2) i).comap greedyMIS ≤ pastMeasurableSpace (q := 3) (i + 2) := by
  simpa [greedyMISOffsets] using
    (FiniteDependence.Coloring.comap_past_le_of_local
      (q := 3) (q' := 2) (f := greedyMIS) (o := greedyMISOffsets) (r := 2)
      (hlocal := measurable_greedyMIS_local)
      (hupper := by
        intro t
        fin_cases t <;> decide)
      i)

private lemma comap_future_le (i : ℤ) :
    (futureMeasurableSpace (q := 2) i 6).comap greedyMIS
      ≤ futureMeasurableSpace (q := 3) (i + 2) 2 := by
  simpa [greedyMISOffsets] using
    (FiniteDependence.Coloring.comap_future_le_of_local
      (q := 3) (q' := 2) (f := greedyMIS) (o := greedyMISOffsets) (r := 2) (k := 2)
      (k' := 6) (hlocal := measurable_greedyMIS_local)
      (hlower := by
        intro t
        fin_cases t <;> decide)
      i)

/-! ### Measurable MIS event -/

end Model

open Model

/-! ## Main application theorem -/

/-- There exists a stationary `6`-dependent `0/1` process on `ℤ` which is almost surely a maximal
independent set (no `11` and no `000`). -/
theorem exists_stationary_sixDependent_MIS :
    ∃ μ : ProbabilityMeasure (ℤ → Fin 2),
      IsStationary μ ∧
      IsKDependent μ 6 ∧
      (μ : Measure (ℤ → Fin 2)) {x | IsMIS x} = 1 := by
  classical
  rcases exists_stationary_twoDependent_threeColoring with ⟨μ3, hstat3, hkdep3, hcol3⟩
  let μ : ProbabilityMeasure (ℤ → Fin 2) := μ3.map Model.measurable_greedyMIS.aemeasurable
  refine ⟨μ, ?_, ?_, ?_⟩
  · -- Stationarity: `greedyMIS` commutes with the shift.
    have hcomm :
        (FiniteDependence.Coloring.shift (q := 2)) ∘ greedyMIS
          = greedyMIS ∘ (FiniteDependence.Coloring.shift (q := 3)) := by
      funext c
      simpa [Function.comp] using (Model.greedyMIS_shift c).symm
    simpa [μ] using
      (FiniteDependence.Coloring.isStationary_map_of_comm
        (hf := Model.measurable_greedyMIS)
        (hcomm := hcomm) (hstat := hstat3))
  · -- 6-dependence: base 2-dependence + radius 2 locality.
    have hkdepMap : FiniteDependence.Coloring.IsKDependent (q := 2) μ 6 :=
      FiniteDependence.Coloring.isKDependent_map_of_past_future
        (hf := Model.measurable_greedyMIS.aemeasurable) (hdep := hkdep3)
        (cut := fun i => i + 2) (hpast := Model.comap_past_le)
        (hfuture := Model.comap_future_le)
    simpa [IsKDependent, μ, ProbabilityMeasure.map] using hkdepMap
  · -- The greedy image of a proper coloring is an MIS, and `μ3` is supported on proper colorings.
    have hpre :
        (μ3 : Measure (ℤ → Fin 3)) (greedyMIS ⁻¹' {x : ℤ → Fin 2 | IsMIS x}) = 1 := by
      have hsub :
          {c : ℤ → Fin 3 | IsColoring (q := 3) c} ⊆ greedyMIS ⁻¹' {x : ℤ → Fin 2 | IsMIS x} := by
        intro c hc
        exact Model.greedyMIS_isMIS_of_isColoring c hc
      have hle :
          (μ3 : Measure (ℤ → Fin 3)) {c : ℤ → Fin 3 | IsColoring (q := 3) c}
            ≤ (μ3 : Measure (ℤ → Fin 3)) (greedyMIS ⁻¹' {x : ℤ → Fin 2 | IsMIS x}) :=
        measure_mono hsub
      have hprob : (μ3 : Measure (ℤ → Fin 3)) Set.univ = 1 := by
        simp
      have hle1 :
          (μ3 : Measure (ℤ → Fin 3)) (greedyMIS ⁻¹' {x : ℤ → Fin 2 | IsMIS x}) ≤ 1 := by
        have : (μ3 : Measure (ℤ → Fin 3)) (greedyMIS ⁻¹' {x : ℤ → Fin 2 | IsMIS x})
            ≤ (μ3 : Measure (ℤ → Fin 3)) Set.univ :=
          measure_mono (subset_univ _)
        simpa [hprob] using this
      have hcol : (μ3 : Measure (ℤ → Fin 3)) {c : ℤ → Fin 3 | IsColoring (q := 3) c} = 1 := hcol3
      have : 1 ≤ (μ3 : Measure (ℤ → Fin 3)) (greedyMIS ⁻¹' {x : ℤ → Fin 2 | IsMIS x}) := by
        simpa [hcol] using hle
      exact le_antisymm hle1 this
    have hmeasMIS : MeasurableSet {x : ℤ → Fin 2 | IsMIS x} := by
      simpa [IsMIS] using (FiniteDependence.measurableSet_isMIS)
    -- Evaluate the pushforward measure on this measurable set.
    have hmap :
        (μ : Measure (ℤ → Fin 2)) {x : ℤ → Fin 2 | IsMIS x}
          = (μ3 : Measure (ℤ → Fin 3)) (greedyMIS ⁻¹' {x : ℤ → Fin 2 | IsMIS x}) := by
      simpa [μ] using (ProbabilityMeasure.map_apply' μ3 Model.measurable_greedyMIS.aemeasurable hmeasMIS)
    calc
      (μ : Measure (ℤ → Fin 2)) {x : ℤ → Fin 2 | IsMIS x}
          = (μ3 : Measure (ℤ → Fin 3)) (greedyMIS ⁻¹' {x : ℤ → Fin 2 | IsMIS x}) := hmap
      _ = 1 := hpre

end FiniteDependence.Coloring
