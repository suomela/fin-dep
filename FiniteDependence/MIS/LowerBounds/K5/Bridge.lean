import FiniteDependence.API.Definitions
import FiniteDependence.Core.Binary

import FiniteDependence.Coloring.DependenceEquivalence
import FiniteDependence.Coloring.MIS
import FiniteDependence.MIS.Core
import FiniteDependence.MIS.K5Results

import Mathlib.MeasureTheory.Measure.Restrict

/-!
# Lower-Bound Bridge for `k = 5`

This module contains the technical bridge from the public `Fin 2`-valued formulation
(`ExistsStationaryKDependentMIS 5`) to the existing lower-bound theorem in
`FiniteDependence.MIS`, which is phrased on the subtype of `Bool`-valued MIS configurations.
-/

namespace FiniteDependence

open MeasureTheory ProbabilityTheory Set

/-! ## Lower bound (nonexistence) -/

namespace LowerBoundBridge

/-!
We bridge from the “human-facing” statement (a probability measure on `ℤ → Fin 2` with
`IsStationary` + cut `k`-dependence + almost-sure MIS support) to the existing lower-bound theorem
in `FiniteDependence.MIS`, which is phrased on the subtype of MIS configurations `ℤ → Bool` with
finite-block `KDependent 5`.
-/

private lemma isMIS_bool_of_isMIS_fin2 {x : ℤ → Fin 2} (hx : IsMIS x) :
    FiniteDependence.MIS.IsMIS (toBoolConfig x) := by
  rcases hx with ⟨h11, h000⟩
  refine ⟨?_, ?_⟩
  · intro i h
    rcases h with ⟨hi, hi1⟩
    have hx1 : x i = (1 : Fin 2) := (toBoolConfig_eq_true_iff x i).1 hi
    have hx2 : x (i + 1) = (1 : Fin 2) := (toBoolConfig_eq_true_iff x (i + 1)).1 hi1
    exact h11 i ⟨hx1, hx2⟩
  · intro i h
    rcases h with ⟨hi, hi1, hi2⟩
    have hx0 : x i = (0 : Fin 2) := (toBoolConfig_eq_false_iff x i).1 hi
    have hx1 : x (i + 1) = (0 : Fin 2) := (toBoolConfig_eq_false_iff x (i + 1)).1 hi1
    have hx2 : x (i + 2) = (0 : Fin 2) := (toBoolConfig_eq_false_iff x (i + 2)).1 hi2
    exact h000 i ⟨hx0, hx1, hx2⟩

private lemma isStationary_toBool (μ : ProbabilityMeasure (ℤ → Fin 2)) (hstat : IsStationary μ) :
    IsStationary (μ.map (aemeasurable_toBoolConfig μ)) := by
  classical
  -- Work on coerced measures.
  change
      (((μ.map (aemeasurable_toBoolConfig μ) : ProbabilityMeasure (ℤ → Bool)) : Measure (ℤ → Bool)).map shift)
        = ((μ.map (aemeasurable_toBoolConfig μ) : ProbabilityMeasure (ℤ → Bool)) : Measure (ℤ → Bool))
  have hmeas_shift_bool : Measurable (shift (α := Bool)) := FiniteDependence.measurable_shift
  have hmeas_shift_fin2 : Measurable (shift (α := Fin 2)) := FiniteDependence.measurable_shift
  have hmeas_toBool : Measurable toBoolConfig := measurable_toBoolConfig
  calc
    ((μ : Measure (ℤ → Fin 2)).map toBoolConfig).map (shift (α := Bool))
        = (μ : Measure (ℤ → Fin 2)).map ((shift (α := Bool)) ∘ toBoolConfig) := by
            simpa using Measure.map_map (μ := (μ : Measure (ℤ → Fin 2))) hmeas_shift_bool hmeas_toBool
    _ = (μ : Measure (ℤ → Fin 2)).map (toBoolConfig ∘ (shift (α := Fin 2))) := by
          have hfun : (shift (α := Bool)) ∘ toBoolConfig = toBoolConfig ∘ (shift (α := Fin 2)) := by
            funext x
            simpa [Function.comp] using (toBoolConfig_shift x).symm
          simpa [hfun]
    _ = ((μ : Measure (ℤ → Fin 2)).map (shift (α := Fin 2))).map toBoolConfig := by
          symm
          simpa using Measure.map_map (μ := (μ : Measure (ℤ → Fin 2))) hmeas_toBool hmeas_shift_fin2
    _ = (μ : Measure (ℤ → Fin 2)).map toBoolConfig := by
          have hstat' :
              ((μ : Measure (ℤ → Fin 2)).map (shift (α := Fin 2))) = (μ : Measure (ℤ → Fin 2)) := hstat
          simpa using congrArg (fun ν : Measure (ℤ → Fin 2) => ν.map toBoolConfig) hstat'

private lemma indepFun_map_iff {Ω Ω' β γ : Type*} [MeasurableSpace Ω] [MeasurableSpace Ω']
    [MeasurableSpace β] [MeasurableSpace γ] {μ : Measure Ω} {f : Ω → Ω'} (hf : Measurable f)
    {X : Ω' → β} {Y : Ω' → γ} (hX : Measurable X) (hY : Measurable Y) :
    (X ⟂ᵢ[μ.map f] Y) ↔ ((X ∘ f) ⟂ᵢ[μ] (Y ∘ f)) := by
  constructor <;> intro h
  · -- Push independence back along `f` using `Measure.map_apply`.
    rw [indepFun_iff_measure_inter_preimage_eq_mul] at h ⊢
    intro s t hs ht
    have hs' : MeasurableSet (X ⁻¹' s) := hX hs
    have ht' : MeasurableSet (Y ⁻¹' t) := hY ht
    have hst' : MeasurableSet (X ⁻¹' s ∩ Y ⁻¹' t) := hs'.inter ht'
    -- Rewrite everything via `map_apply`.
    simpa [Measure.map_apply hf hs', Measure.map_apply hf ht', Measure.map_apply hf hst',
      preimage_inter, Function.comp] using h (s := s) (t := t) hs ht
  · -- Push independence forward along `f` using `Measure.map_apply`.
    rw [indepFun_iff_measure_inter_preimage_eq_mul] at h ⊢
    intro s t hs ht
    have hs' : MeasurableSet (X ⁻¹' s) := hX hs
    have ht' : MeasurableSet (Y ⁻¹' t) := hY ht
    have hst' : MeasurableSet (X ⁻¹' s ∩ Y ⁻¹' t) := hs'.inter ht'
    -- Rewrite everything via `map_apply`.
    simpa [Measure.map_apply hf hs', Measure.map_apply hf ht', Measure.map_apply hf hst',
      preimage_inter, Function.comp] using h (s := s) (t := t) hs ht

private def blockSet (a : ℤ) (n : ℕ) : Set ℤ :=
  {i | ∃ j : Fin n, i = a + Int.ofNat j.1}

private def block {α : Type*} (a : ℤ) (n : ℕ) : (ℤ → α) → (Fin n → α) :=
  fun x j => x (a + Int.ofNat j.1)

private abbrev coordMeasurableSpaceConfig {α : Type*} [MeasurableSpace α] (S : Set ℤ) :
    MeasurableSpace (ℤ → α) :=
  FiniteDependence.coordMeasurableSpace (coord := fun x : ℤ → α => x) S

private lemma measurable_apply_coord {α : Type*} [MeasurableSpace α] {S : Set ℤ} {i : ℤ} (hi : i ∈ S) :
    Measurable[coordMeasurableSpaceConfig (α := α) S] (fun x : ℤ → α => x i) := by
  have hle :
      MeasurableSpace.comap (fun x : ℤ → α => x i) inferInstance
        ≤ coordMeasurableSpaceConfig (α := α) S := by
    classical
    unfold coordMeasurableSpaceConfig FiniteDependence.coordMeasurableSpace
    exact le_iSup
      (fun j : {j : ℤ // j ∈ S} =>
        MeasurableSpace.comap (fun x : ℤ → α => x j.1) inferInstance) ⟨i, hi⟩
  exact Measurable.of_comap_le hle

private lemma measurable_block_coord {α : Type*} [MeasurableSpace α] (a : ℤ) (n : ℕ) :
    Measurable[coordMeasurableSpaceConfig (α := α) (blockSet a n)] (block (α := α) a n) := by
  classical
  -- Work in the coordinate σ-algebra on exactly the indices in the block.
  letI : MeasurableSpace (ℤ → α) := coordMeasurableSpaceConfig (α := α) (blockSet a n)
  refine measurable_pi_lambda _ (fun j => ?_)
  have hj : a + Int.ofNat j.1 ∈ blockSet a n := ⟨j, rfl⟩
  simpa [block] using
    (measurable_apply_coord (α := α) (S := blockSet a n) (i := a + Int.ofNat j.1) hj)

private lemma indexSeparated_blockSet {a b : ℤ} {m n k : ℕ}
    (hsep :
      ∀ i : Fin m, ∀ j : Fin n,
        Int.natAbs ((a + Int.ofNat i.1) - (b + Int.ofNat j.1)) > k) :
    IndexSeparated (blockSet a m) (blockSet b n) k := by
  intro a' ha' b' hb'
  rcases ha' with ⟨i, rfl⟩
  rcases hb' with ⟨j, rfl⟩
  -- Rewrite into the given separation hypothesis.
  simpa [sub_eq_add_neg, add_assoc, add_left_comm, add_comm] using hsep i j

private lemma indepFun_block_fin2_of_noncontig (μ : ProbabilityMeasure (ℤ → Fin 2)) {k m n : ℕ} {a b : ℤ}
    (hdep : IsKDependentNoncontigConfig μ k)
    (hsep :
      ∀ i : Fin m, ∀ j : Fin n,
        Int.natAbs ((a + Int.ofNat i.1) - (b + Int.ofNat j.1)) > k) :
    (block (α := Fin 2) a m) ⟂ᵢ[(μ : Measure (ℤ → Fin 2))] (block (α := Fin 2) b n) := by
  -- Independence of the coordinate σ-algebras.
  have hind :
      Indep (coordMeasurableSpaceConfig (α := Fin 2) (blockSet a m))
        (coordMeasurableSpaceConfig (α := Fin 2) (blockSet b n)) (μ := (μ : Measure (ℤ → Fin 2))) := by
    refine hdep (A := blockSet a m) (B := blockSet b n) ?_
    exact indexSeparated_blockSet (a := a) (b := b) (m := m) (n := n) (k := k) hsep
  -- `block a m` is measurable w.r.t. its coordinate σ-algebra (hence its comap is ≤).
  have hcomapA :
      MeasurableSpace.comap (block (α := Fin 2) a m) inferInstance
        ≤ coordMeasurableSpaceConfig (α := Fin 2) (blockSet a m) :=
    (measurable_block_coord (α := Fin 2) (a := a) (n := m)).comap_le
  have hcomapB :
      MeasurableSpace.comap (block (α := Fin 2) b n) inferInstance
        ≤ coordMeasurableSpaceConfig (α := Fin 2) (blockSet b n) :=
    (measurable_block_coord (α := Fin 2) (a := b) (n := n)).comap_le
  -- Restrict the independent σ-algebras to these comaps and use `IndepFun_iff_Indep`.
  have hind' :
      Indep (MeasurableSpace.comap (block (α := Fin 2) a m) inferInstance)
        (MeasurableSpace.comap (block (α := Fin 2) b n) inferInstance) (μ := (μ : Measure (ℤ → Fin 2))) := by
    have h1 := ProbabilityTheory.indep_of_indep_of_le_left (μ := (μ : Measure (ℤ → Fin 2))) hind hcomapA
    exact ProbabilityTheory.indep_of_indep_of_le_right (μ := (μ : Measure (ℤ → Fin 2))) h1 hcomapB
  exact (IndepFun_iff_Indep (f := block (α := Fin 2) a m) (g := block (α := Fin 2) b n)
    (μ := (μ : Measure (ℤ → Fin 2)))).2 hind'

private def blockFin2ToBool (n : ℕ) : (Fin n → Fin 2) → (Fin n → Bool) :=
  fun w j => fin2ToBool (w j)

private lemma measurable_blockFin2ToBool (n : ℕ) : Measurable (blockFin2ToBool n) := by
  classical
  -- The domain is finite, hence discrete measurable.
  simpa [blockFin2ToBool] using (Measurable.of_discrete : Measurable (fun w : Fin n → Fin 2 => fun j => fin2ToBool (w j)))

private lemma block_bool_comp_toBoolConfig (a : ℤ) (n : ℕ) :
    (block (α := Bool) a n) ∘ toBoolConfig = (blockFin2ToBool n) ∘ (block (α := Fin 2) a n) := by
  funext x
  ext j
  simp [block, toBoolConfig, blockFin2ToBool, Function.comp]

private lemma measurable_block_config {α : Type*} [MeasurableSpace α] (a : ℤ) (n : ℕ) :
    Measurable (block (α := α) a n) := by
  classical
  refine measurable_pi_lambda _ (fun j => ?_)
  simpa [block] using (measurable_pi_apply (a := a + Int.ofNat j.1))

private lemma measurableSet_isMIS_bool :
    MeasurableSet {x : ℤ → Bool | FiniteDependence.MIS.IsMIS x} := by
  classical
  -- Independence constraint (`11` forbidden).
  have h11_single (i : ℤ) :
      MeasurableSet {x : ℤ → Bool | x i = true ∧ x (i + 1) = true} := by
    have hmeas : Measurable fun x : ℤ → Bool => (x i, x (i + 1)) :=
      (measurable_pi_apply (a := i)).prodMk (measurable_pi_apply (a := i + 1))
    simpa [Set.preimage, Set.mem_singleton_iff] using
      (measurableSet_singleton (true, true)).preimage hmeas
  have h11_comp (i : ℤ) :
      MeasurableSet {x : ℤ → Bool | ¬(x i = true ∧ x (i + 1) = true)} :=
    (h11_single i).compl
  have h11 :
      MeasurableSet {x : ℤ → Bool | ∀ i : ℤ, ¬(x i = true ∧ x (i + 1) = true)} := by
    have hEq :
        ({x : ℤ → Bool | ∀ i : ℤ, ¬(x i = true ∧ x (i + 1) = true)}
          = ⋂ i : ℤ, {x : ℤ → Bool | ¬(x i = true ∧ x (i + 1) = true)}) := by
      ext x
      simp
    rw [hEq]
    exact MeasurableSet.iInter h11_comp

  -- Maximality constraint (`000` forbidden).
  have h000_single (i : ℤ) :
      MeasurableSet {x : ℤ → Bool | x i = false ∧ x (i + 1) = false ∧ x (i + 2) = false} := by
    have hmeas : Measurable fun x : ℤ → Bool => (x i, x (i + 1), x (i + 2)) :=
      (measurable_pi_apply (a := i)).prodMk
        ((measurable_pi_apply (a := i + 1)).prodMk (measurable_pi_apply (a := i + 2)))
    simpa [Set.preimage, Set.mem_singleton_iff, and_assoc] using
      (measurableSet_singleton (false, false, false)).preimage hmeas
  have h000_comp (i : ℤ) :
      MeasurableSet {x : ℤ → Bool | ¬(x i = false ∧ x (i + 1) = false ∧ x (i + 2) = false)} :=
    (h000_single i).compl
  have h000 :
      MeasurableSet {x : ℤ → Bool | ∀ i : ℤ, ¬(x i = false ∧ x (i + 1) = false ∧ x (i + 2) = false)} := by
    have hEq :
        ({x : ℤ → Bool | ∀ i : ℤ, ¬(x i = false ∧ x (i + 1) = false ∧ x (i + 2) = false)}
          = ⋂ i : ℤ, {x : ℤ → Bool | ¬(x i = false ∧ x (i + 1) = false ∧ x (i + 2) = false)}) := by
      ext x
      simp
    rw [hEq]
    exact MeasurableSet.iInter h000_comp

  -- Combine.
  have hEq :
      ({x : ℤ → Bool | FiniteDependence.MIS.IsMIS x}
        = {x : ℤ → Bool | ∀ i : ℤ, ¬(x i = true ∧ x (i + 1) = true)}
            ∩ {x : ℤ → Bool | ∀ i : ℤ, ¬(x i = false ∧ x (i + 1) = false ∧ x (i + 2) = false)}) := by
    ext x
    simp [FiniteDependence.MIS.IsMIS]
  simpa [hEq] using h11.inter h000

private lemma prob_isMIS_toBoolConfig (μ : ProbabilityMeasure (ℤ → Fin 2))
    (hMIS : (μ : Measure (ℤ → Fin 2)) {x | IsMIS x} = 1) :
    ((μ.map (aemeasurable_toBoolConfig μ) : ProbabilityMeasure (ℤ → Bool)) : Measure (ℤ → Bool))
        {x | FiniteDependence.MIS.IsMIS x} = 1 := by
  classical
  -- Unfold the mapped probability measure.
  change ((μ : Measure (ℤ → Fin 2)).map toBoolConfig) {x | FiniteDependence.MIS.IsMIS x} = 1
  -- Rewrite via `map_apply`.
  have hmap :
      ((μ : Measure (ℤ → Fin 2)).map toBoolConfig) {x | FiniteDependence.MIS.IsMIS x}
        = (μ : Measure (ℤ → Fin 2)) (toBoolConfig ⁻¹' {x | FiniteDependence.MIS.IsMIS x}) := by
    simpa using
      (Measure.map_apply (μ := (μ : Measure (ℤ → Fin 2))) (f := toBoolConfig) measurable_toBoolConfig
        measurableSet_isMIS_bool)
  -- `IsMIS` pushes forward pointwise.
  have hsub : {x : ℤ → Fin 2 | IsMIS x} ⊆ toBoolConfig ⁻¹' {x : ℤ → Bool | FiniteDependence.MIS.IsMIS x} := by
    intro x hx
    exact isMIS_bool_of_isMIS_fin2 (x := x) hx
  have hge :
      (1 : ENNReal) ≤ (μ : Measure (ℤ → Fin 2)) (toBoolConfig ⁻¹' {x : ℤ → Bool | FiniteDependence.MIS.IsMIS x}) := by
    have := measure_mono (μ := (μ : Measure (ℤ → Fin 2))) hsub
    simpa [hMIS] using this
  have hle :
      (μ : Measure (ℤ → Fin 2)) (toBoolConfig ⁻¹' {x : ℤ → Bool | FiniteDependence.MIS.IsMIS x})
        ≤ 1 := by
    calc
      (μ : Measure (ℤ → Fin 2)) (toBoolConfig ⁻¹' {x : ℤ → Bool | FiniteDependence.MIS.IsMIS x})
          ≤ (μ : Measure (ℤ → Fin 2)) univ := by
              exact measure_mono (μ := (μ : Measure (ℤ → Fin 2))) (subset_univ _)
      _ = 1 := by
            simp
  have hEq :
      (μ : Measure (ℤ → Fin 2)) (toBoolConfig ⁻¹' {x : ℤ → Bool | FiniteDependence.MIS.IsMIS x}) = 1 :=
    le_antisymm hle hge
  simpa [hmap, hEq]

private lemma indepFun_block_bool_of_noncontig (μ : ProbabilityMeasure (ℤ → Fin 2)) {k m n : ℕ} {a b : ℤ}
    (hdep : IsKDependentNoncontigConfig μ k)
    (hsep :
      ∀ i : Fin m, ∀ j : Fin n,
        Int.natAbs ((a + Int.ofNat i.1) - (b + Int.ofNat j.1)) > k) :
    (block (α := Bool) a m)
      ⟂ᵢ[((μ.map (aemeasurable_toBoolConfig μ) : ProbabilityMeasure (ℤ → Bool)) : Measure (ℤ → Bool))]
        (block (α := Bool) b n) := by
  -- First get independence of `Fin 2` blocks under `μ`.
  have hFin2 :
      (block (α := Fin 2) a m) ⟂ᵢ[(μ : Measure (ℤ → Fin 2))] (block (α := Fin 2) b n) :=
    indepFun_block_fin2_of_noncontig (μ := μ) (hdep := hdep) (hsep := hsep)
  -- Apply a measurable postprocessing map to each block.
  have hComp :
      ((block (α := Bool) a m) ∘ toBoolConfig) ⟂ᵢ[(μ : Measure (ℤ → Fin 2))] ((block (α := Bool) b n) ∘ toBoolConfig) := by
    have hComp' :
        ((blockFin2ToBool m) ∘ (block (α := Fin 2) a m))
          ⟂ᵢ[(μ : Measure (ℤ → Fin 2))] ((blockFin2ToBool n) ∘ (block (α := Fin 2) b n)) :=
      IndepFun.comp hFin2 (measurable_blockFin2ToBool m) (measurable_blockFin2ToBool n)
    simpa [block_bool_comp_toBoolConfig, Function.comp] using hComp'
  -- Transfer to the mapped measure on `ℤ → Bool`.
  have hX : Measurable (block (α := Bool) a m) := measurable_block_config (α := Bool) a m
  have hY : Measurable (block (α := Bool) b n) := measurable_block_config (α := Bool) b n
  have hf : Measurable toBoolConfig := measurable_toBoolConfig
  -- Use the reverse direction of `indepFun_map_iff`.
  have hMap :
      (block (α := Bool) a m) ⟂ᵢ[((μ : Measure (ℤ → Fin 2)).map toBoolConfig)] (block (α := Bool) b n) :=
    (indepFun_map_iff (μ := (μ : Measure (ℤ → Fin 2))) (f := toBoolConfig) hf hX hY).2 hComp
  simpa using hMap

/-- There is no stationary `5`-dependent MIS law in the public `Fin 2` interface. -/
theorem not_exists_stationary_fiveDependent_MIS : ¬ ExistsStationaryKDependentMIS 5 := by
  intro h
  rcases h with ⟨μ, hμ⟩
  rcases hμ with ⟨hstat, hkdep, hMIS⟩
  -- Convert cut dependence to the noncontiguous form (using the existing equivalence for `Fin q`).
  have hkdep_cut' : FiniteDependence.Coloring.IsKDependent (q := 2) μ 5 := by
    simpa [IsKDependentCut, FiniteDependence.Coloring.IsKDependent] using hkdep
  have hkdep_non' : FiniteDependence.Coloring.IsKDependentNoncontig (q := 2) μ 5 :=
    FiniteDependence.Coloring.DependenceEquivalence.isKDependentNoncontig_of_isKDependent (q := 2)
      (μ := μ) hkdep_cut'
  have hkdep_non : IsKDependentNoncontigConfig μ 5 := by
    simpa [IsKDependentNoncontigConfig, FiniteDependence.Coloring.IsKDependentNoncontig] using hkdep_non'

  -- Push the `Fin 2` process to a `Bool`-valued process (pointwise).
  let μBool : ProbabilityMeasure (ℤ → Bool) := μ.map (aemeasurable_toBoolConfig μ)
  have hstatBool : IsStationary μBool :=
    LowerBoundBridge.isStationary_toBool (μ := μ) hstat
  have hMISBool :
      ((μBool : Measure (ℤ → Bool)) {x | FiniteDependence.MIS.IsMIS x} = 1) := by
    simpa [μBool] using LowerBoundBridge.prob_isMIS_toBoolConfig (μ := μ) hMIS

  -- Define the induced probability measure on the subtype of MIS configurations.
  let sMIS : Set (ℤ → Bool) := {x | FiniteDependence.MIS.IsMIS x}
  have hsMIS : MeasurableSet sMIS := LowerBoundBridge.measurableSet_isMIS_bool
  let μState : Measure FiniteDependence.MIS.State :=
    Measure.comap ((↑) : FiniteDependence.MIS.State → (ℤ → Bool)) (μBool : Measure (ℤ → Bool))

  have hμMIS_univ : μState univ = 1 := by
    -- `μState univ = μBool sMIS`.
    have hcomap :
        (Measure.comap ((↑) : FiniteDependence.MIS.State → (ℤ → Bool)) (μBool : Measure (ℤ → Bool))) univ
          = (μBool : Measure (ℤ → Bool)) (((↑) : FiniteDependence.MIS.State → (ℤ → Bool)) '' (univ : Set FiniteDependence.MIS.State)) :=
      comap_subtype_coe_apply (α := (ℤ → Bool)) (s := sMIS) hsMIS
        (μ := (μBool : Measure (ℤ → Bool))) (t := (univ : Set FiniteDependence.MIS.State))
    have hImage :
        (((↑) : FiniteDependence.MIS.State → (ℤ → Bool)) '' (univ : Set FiniteDependence.MIS.State)) = sMIS := by
      ext x
      constructor
      · rintro ⟨ω, -, rfl⟩
        exact ω.2
      · intro hx
        refine ⟨⟨x, hx⟩, by simp, rfl⟩
    -- Finish using `μBool(sMIS)=1`.
    have hcomap' : μState univ = (μBool : Measure (ℤ → Bool)) sMIS := by
      simpa [μState, hImage] using hcomap
    exact hcomap'.trans hMISBool

  classical
  -- Make the `IsProbabilityMeasure` instance available.
  letI : IsProbabilityMeasure μState := ⟨hμMIS_univ⟩

  -- Identify `μBool` as the pushforward of `μState` by coercion.
  have hmap_coe : (μState.map ((↑) : FiniteDependence.MIS.State → (ℤ → Bool))) = (μBool : Measure (ℤ → Bool)) := by
    have hmap :=
      map_comap_subtype_coe (α := (ℤ → Bool)) (s := sMIS) hsMIS (μ := (μBool : Measure (ℤ → Bool)))
    have hae : (∀ᵐ x ∂(μBool : Measure (ℤ → Bool)), x ∈ sMIS) := by
      -- `sMIS` has probability `1` under `μBool`.
      simpa [sMIS] using (mem_ae_iff_prob_eq_one (μ := (μBool : Measure (ℤ → Bool))) hsMIS).2 hMISBool
    have hrestrip : (μBool : Measure (ℤ → Bool)).restrict sMIS = (μBool : Measure (ℤ → Bool)) :=
      Measure.restrict_eq_self_of_ae_mem hae
    simpa [μState, hrestrip, sMIS] using hmap

  -- Stationarity transfers to the subtype by injectivity of `map` along a measurable embedding.
  have hstatMIS : FiniteDependence.MIS.Model.Stationary μState := by
    -- It suffices to check equality after mapping by the coercion to configurations.
    apply (MeasurableEmbedding.map_injective (MeasurableEmbedding.subtype_coe hsMIS))
    have hmeas_coe : Measurable ((↑) : FiniteDependence.MIS.State → (ℤ → Bool)) := measurable_subtype_coe
    have hmeas_shiftSub : Measurable (FiniteDependence.MIS.Model.shift (1 : ℤ)) :=
      FiniteDependence.MIS.Model.measurable_shift (1 : ℤ)
    have hmeas_shiftCfg : Measurable (shift (α := Bool)) := FiniteDependence.measurable_shift
    -- Commute the shift with coercion.
    have hcomm :
        ((↑) : FiniteDependence.MIS.State → (ℤ → Bool)) ∘ FiniteDependence.MIS.Model.shift (1 : ℤ)
          = (shift (α := Bool)) ∘ ((↑) : FiniteDependence.MIS.State → (ℤ → Bool)) := by
      funext ω
      ext i
      simp [FiniteDependence.MIS.Model.shift, shift, FiniteDependence.shift, add_assoc]
    -- Compute both sides in `Measure (ℤ → Bool)`.
    calc
      (μState.map (FiniteDependence.MIS.Model.shift (1 : ℤ))).map ((↑) : FiniteDependence.MIS.State → (ℤ → Bool))
          = μState.map (((↑) : FiniteDependence.MIS.State → (ℤ → Bool)) ∘ FiniteDependence.MIS.Model.shift (1 : ℤ)) := by
              simpa using Measure.map_map (μ := μState) hmeas_coe hmeas_shiftSub
      _ = μState.map ((shift (α := Bool)) ∘ ((↑) : FiniteDependence.MIS.State → (ℤ → Bool))) := by
            simp [hcomm]
      _ = ((μState.map ((↑) : FiniteDependence.MIS.State → (ℤ → Bool))).map (shift (α := Bool))) := by
            symm
            simpa using Measure.map_map (μ := μState) hmeas_shiftCfg hmeas_coe
      _ = (μBool : Measure (ℤ → Bool)) := by
            -- Use stationarity of `μBool`.
            have : ((μBool : Measure (ℤ → Bool)).map (shift (α := Bool))) = (μBool : Measure (ℤ → Bool)) :=
              hstatBool
            simpa [hmap_coe] using this
      _ = μState.map ((↑) : FiniteDependence.MIS.State → (ℤ → Bool)) := by
            symm
            exact hmap_coe

  -- `KDependent 5` transfers similarly, using independence of blocks under `μBool`.
  have hdepMIS : FiniteDependence.MIS.Model.KDependent 5 μState := by
    intro a b m n hsep
    -- Independence of the corresponding blocks under `μBool` (pulled from `μ`).
    have hIndBool :
        (LowerBoundBridge.block (α := Bool) a m)
          ⟂ᵢ[(μBool : Measure (ℤ → Bool))] (LowerBoundBridge.block (α := Bool) b n) := by
      simpa [μBool] using
        LowerBoundBridge.indepFun_block_bool_of_noncontig (μ := μ) (hdep := hkdep_non) (hsep := hsep)
    -- Pull back independence along the coercion `State → Config`.
    have hIndOnMIS :
        ((LowerBoundBridge.block (α := Bool) a m) ∘ ((↑) : FiniteDependence.MIS.State → (ℤ → Bool)))
          ⟂ᵢ[μState]
            ((LowerBoundBridge.block (α := Bool) b n) ∘ ((↑) : FiniteDependence.MIS.State → (ℤ → Bool))) := by
      have hX : Measurable (LowerBoundBridge.block (α := Bool) a m) :=
        LowerBoundBridge.measurable_block_config (α := Bool) a m
      have hY : Measurable (LowerBoundBridge.block (α := Bool) b n) :=
        LowerBoundBridge.measurable_block_config (α := Bool) b n
      have hf : Measurable ((↑) : FiniteDependence.MIS.State → (ℤ → Bool)) := measurable_subtype_coe
      -- Rewrite `μBool` as `μState.map coe` and apply `indepFun_map_iff`.
      have hIndMap :
          (LowerBoundBridge.block (α := Bool) a m) ⟂ᵢ[(μState.map ((↑) : FiniteDependence.MIS.State → (ℤ → Bool)))]
            (LowerBoundBridge.block (α := Bool) b n) := by
        simpa [hmap_coe] using hIndBool
      exact (LowerBoundBridge.indepFun_map_iff (μ := μState) (f := ((↑) : FiniteDependence.MIS.State → (ℤ → Bool)))
        hf hX hY).1 hIndMap
    -- Identify these functions with `FiniteDependence.MIS.Model.block`.
    simpa [FiniteDependence.MIS.Model.block, LowerBoundBridge.block, Function.comp]
      using hIndOnMIS

  -- Contradiction with the established lower bound.
  exact FiniteDependence.MIS.no_stationary_fiveDependent_MIS (μ := μState) hstatMIS hdepMIS

end LowerBoundBridge

end FiniteDependence
