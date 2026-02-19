import Mathlib
import FiniteDependence.Core.Process

namespace FiniteDependence.MIS

open MeasureTheory Set

open scoped BigOperators ProbabilityTheory

/-!
## A probability model for MIS on `ℤ`

This file sets up the basic measurable/probabilistic objects needed to state the
“full” impossibility theorems:

- the sample space `State`, consisting of bi-infinite 0/1 sequences on `ℤ` satisfying
  the MIS constraints (forbid `11` and `000`), and
- cylinder events (`cyl`) and the shift map (`shift`),
- basic notions of stationarity and `k`-dependence (restricted to finite blocks).

The files `K3Kernel.lean` and `K4Kernel.lean` formalize the *algebraic endgames*.
The file `K3Model.lean` derives the model-level `k=3` contradiction from those kernels.
-/

/-- A bi-infinite 0/1 configuration on `ℤ`. `true` means “occupied”. -/
abbrev Config : Type := ℤ → Bool

/-- The MIS shift of finite type on `ℤ`: forbid `11` and `000`. -/
def IsMIS (ω : Config) : Prop :=
  (∀ i : ℤ, ¬(ω i = true ∧ ω (i + 1) = true)) ∧
    (∀ i : ℤ, ¬(ω i = false ∧ ω (i + 1) = false ∧ ω (i + 2) = false))

/-- The state space of MIS configurations. -/
abbrev State : Type := { ω : Config // IsMIS ω }

noncomputable section

namespace Model

/-- Shift the configuration by `n` steps: `(shift n ω) i = ω (i+n)`. -/
def shift (n : ℤ) (ω : State) : State :=
  ⟨fun i => ω.1 (i + n), by
    rcases ω.2 with ⟨h11, h000⟩
    refine ⟨?_, ?_⟩
    · intro i
      simpa [add_assoc, add_left_comm, add_comm] using (h11 (i + n))
    · intro i
      simpa [add_assoc, add_left_comm, add_comm] using (h000 (i + n))⟩

theorem measurable_shift (n : ℤ) : Measurable (shift n) := by
  classical
  have hval : Measurable (fun ω : State => (fun i => ω.1 (i + n) : Config)) := by
    refine measurable_pi_iff.mpr ?_
    intro i
    simpa using (measurable_pi_apply (i + n)).comp measurable_subtype_coe
  exact hval.subtype_mk

/-! ### Cylinder events -/

/-- Projection to a contiguous block of length `n`, starting at position `a`. -/
def block (a : ℤ) (n : ℕ) : State → (Fin n → Bool) :=
  fun ω j => ω.1 (a + Int.ofNat j.1)

theorem measurable_block (a : ℤ) (n : ℕ) : Measurable (block a n) := by
  classical
  refine measurable_pi_iff.mpr ?_
  intro j
  simpa [block] using (measurable_pi_apply (a + Int.ofNat j.1)).comp measurable_subtype_coe

/-- The cylinder set of a word `w` at position `a`. -/
def cyl {n : ℕ} (a : ℤ) (w : Fin n → Bool) : Set State :=
  { ω | block a n ω = w }

theorem cyl_eq_preimage {n : ℕ} (a : ℤ) (w : Fin n → Bool) :
    cyl a w = block a n ⁻¹' ({w} : Set (Fin n → Bool)) := by
  ext ω
  simp [cyl]

theorem disjoint_cyl_of_ne {n : ℕ} (a : ℤ) {u v : Fin n → Bool} (huv : u ≠ v) :
    Disjoint (cyl a u) (cyl a v) := by
  refine disjoint_left.2 ?_
  intro ω hu hv
  apply huv
  simpa [cyl] using (hu.symm.trans hv)

theorem measurableSet_cyl {n : ℕ} (a : ℤ) (w : Fin n → Bool) : MeasurableSet (cyl a w) := by
  classical
  have hb : Measurable (block a n) := measurable_block a n
  have hs : MeasurableSet ({w} : Set (Fin n → Bool)) := measurableSet_singleton w
  have : MeasurableSet (block a n ⁻¹' ({w} : Set (Fin n → Bool))) :=
    MeasurableSet.preimage hs hb
  simpa [cyl, Set.preimage, Set.mem_singleton_iff] using this

theorem measure_union_cyl_of_ne (μ : Measure State) (a : ℤ) {n : ℕ} {u v : Fin n → Bool}
    (huv : u ≠ v) : μ (cyl a u ∪ cyl a v) = μ (cyl a u) + μ (cyl a v) := by
  refine measure_union ?_ ?_
  · exact disjoint_cyl_of_ne (a := a) huv
  · exact measurableSet_cyl a v

theorem bit_eq_of_block_eq {n : ℕ} {a : ℤ} {w : Fin n → Bool} {ω : State}
    (h : block a n ω = w) (i : Fin n) : ω.1 (a + Int.ofNat i.1) = w i := by
  have hi := congrArg (fun f : Fin n → Bool => f i) h
  simpa [block] using hi

theorem bit_eq_of_mem_cyl {n : ℕ} {a : ℤ} {w : Fin n → Bool} {ω : State}
    (h : ω ∈ cyl a w) (i : Fin n) : ω.1 (a + Int.ofNat i.1) = w i := by
  have hblock : block a n ω = w := by
    simpa [cyl] using h
  exact bit_eq_of_block_eq hblock i

theorem block_shift (a : ℤ) (n : ℕ) (ω : State) :
    block a n (shift (1 : ℤ) ω) = block (a + 1) n ω := by
  funext j
  simp [block, shift, add_assoc, add_left_comm, add_comm]

theorem preimage_shift_cyl {n : ℕ} (a : ℤ) (w : Fin n → Bool) :
    shift (1 : ℤ) ⁻¹' cyl a w = cyl (a + 1) w := by
  ext ω
  constructor <;> intro h
  · have : block (a + 1) n ω = w := by
      simpa [cyl, block_shift] using h
    simpa [cyl] using this
  · have : block a n (shift (1 : ℤ) ω) = w := by
      simpa [block_shift] using h
    simpa [cyl] using this

/-! ### Stationarity and finite-block `k`-dependence -/

/-- Stationarity (shift-invariance) under the 1-step shift. -/
def Stationary (μ : Measure State) : Prop :=
  μ.map (shift (1 : ℤ)) = μ

/-- Alias for `Stationary`, matching the naming convention used elsewhere in the repository. -/
abbrev IsStationary (μ : Measure State) : Prop :=
  Stationary μ

/--
Finite-block `k`-dependence: any two finite blocks whose coordinates are pairwise at
distance `> k` are independent.

This is a convenient “cylinder-level” formulation; it is strong enough for the
finite-length contradictions used in `PROOF_k_le_5.md`.
-/
def KDependent (k : ℕ) (μ : Measure State) : Prop :=
  ∀ a b m n,
    (∀ i : Fin m, ∀ j : Fin n,
        Int.natAbs ((a + Int.ofNat i.1) - (b + Int.ofNat j.1)) > k) →
      (block a m) ⟂ᵢ[μ] (block b n)

/-- Coordinate σ-algebra generated by indices `< i`, for the MIS process. -/
abbrev pastMeasurableSpace (i : ℤ) : MeasurableSpace State :=
  FiniteDependence.pastMeasurableSpace (coord := fun ω : State => ω.1) i

/-- Coordinate σ-algebra generated by indices `≥ i + k`, for the MIS process. -/
abbrev futureMeasurableSpace (i : ℤ) (k : ℕ) : MeasurableSpace State :=
  FiniteDependence.futureMeasurableSpace (coord := fun ω : State => ω.1) i k

/-- Coordinate σ-algebra generated by indices in a set `S`, for the MIS process. -/
abbrev coordMeasurableSpace (S : Set ℤ) : MeasurableSpace State :=
  FiniteDependence.coordMeasurableSpace (coord := fun ω : State => ω.1) S

/-- `k`-separation of index sets (shared definition). -/
abbrev IndexSeparated (A B : Set ℤ) (k : ℕ) : Prop :=
  FiniteDependence.IndexSeparated A B k

/-- `k`-dependence in the Holroyd–Liggett “cut” form, phrased via coordinate σ-algebras. -/
abbrev IsKDependent (k : ℕ) (μ : Measure State) : Prop :=
  FiniteDependence.IsKDependent (coord := fun ω : State => ω.1) μ k

/-- `k`-dependence in the noncontiguous form, phrased via coordinate σ-algebras. -/
abbrev IsKDependentNoncontig (k : ℕ) (μ : Measure State) : Prop :=
  FiniteDependence.IsKDependentNoncontig (coord := fun ω : State => ω.1) μ k

/-! ### Basic pointwise consequences of `IsMIS` -/

theorem true_next_false (ω : State) {i : ℤ} (hi : ω.1 i = true) : ω.1 (i + 1) = false := by
  rcases ω.2 with ⟨h11, -⟩
  have hnot : ¬(ω.1 i = true ∧ ω.1 (i + 1) = true) := h11 i
  cases h1 : ω.1 (i + 1)
  · simpa using h1
  · exfalso
    apply hnot
    exact ⟨hi, by simpa using h1⟩

theorem true_prev_false (ω : State) {i : ℤ} (hi : ω.1 (i + 1) = true) : ω.1 i = false := by
  rcases ω.2 with ⟨h11, -⟩
  have hnot : ¬(ω.1 i = true ∧ ω.1 (i + 1) = true) := h11 i
  cases h0 : ω.1 i
  · simpa using h0
  · exfalso
    apply hnot
    exact ⟨by simpa using h0, hi⟩

theorem twoZeros_next_true (ω : State) {i : ℤ} (h0 : ω.1 i = false) (h1 : ω.1 (i + 1) = false) :
    ω.1 (i + 2) = true := by
  rcases ω.2 with ⟨-, h000⟩
  have hnot : ¬(ω.1 i = false ∧ ω.1 (i + 1) = false ∧ ω.1 (i + 2) = false) := h000 i
  cases h2 : ω.1 (i + 2)
  · exfalso
    apply hnot
    exact ⟨h0, h1, h2⟩
  · simpa using h2

theorem twoZeros_prev_true (ω : State) {i : ℤ} (h1 : ω.1 (i + 1) = false) (h2 : ω.1 (i + 2) = false) :
    ω.1 i = true := by
  rcases ω.2 with ⟨-, h000⟩
  have hnot : ¬(ω.1 i = false ∧ ω.1 (i + 1) = false ∧ ω.1 (i + 2) = false) := h000 i
  cases h0 : ω.1 i
  · exfalso
    apply hnot
    exact ⟨h0, h1, h2⟩
  · simpa using h0

theorem Stationary.measure_cyl_succ {μ : Measure State} (hμ : Stationary μ) {n : ℕ} (a : ℤ)
    (w : Fin n → Bool) : μ (cyl (a + 1) w) = μ (cyl a w) := by
  have happly : (μ.map (shift (1 : ℤ))) (cyl a w) = μ (cyl a w) :=
    congrArg (fun ν : Measure State => ν (cyl a w)) hμ
  have hmeas : MeasurableSet (cyl a w) := measurableSet_cyl a w
  have : μ (shift (1 : ℤ) ⁻¹' cyl a w) = μ (cyl a w) := by
    simpa [Measure.map_apply (measurable_shift (1 : ℤ)) hmeas] using happly
  simpa [preimage_shift_cyl] using this

theorem Stationary.measure_cyl_add_nat {μ : Measure State} (hμ : Stationary μ) {n : ℕ} (a : ℤ)
    (s : ℕ) (w : Fin n → Bool) : μ (cyl (a + s) w) = μ (cyl a w) := by
  induction s with
  | zero =>
      simp
  | succ s ih =>
      calc
        μ (cyl (a + Nat.succ s) w)
            = μ (cyl ((a + s) + 1) w) := by
                simp [Nat.cast_add, Nat.cast_one, add_assoc, add_left_comm, add_comm]
        _ = μ (cyl (a + s) w) :=
              Stationary.measure_cyl_succ (μ := μ) hμ (a := a + s) (w := w)
        _ = μ (cyl a w) := ih

theorem KDependent.measure_inter_cyl_eq_mul {μ : Measure State} {k m n : ℕ} {a b : ℤ}
    (hμ : KDependent k μ)
    (hsep :
      ∀ i : Fin m, ∀ j : Fin n,
        Int.natAbs ((a + Int.ofNat i.1) - (b + Int.ofNat j.1)) > k)
    (w : Fin m → Bool) (v : Fin n → Bool) :
    μ (cyl a w ∩ cyl b v) = μ (cyl a w) * μ (cyl b v) := by
  have hind : (block a m) ⟂ᵢ[μ] (block b n) := hμ a b m n hsep
  have hs : MeasurableSet ({w} : Set (Fin m → Bool)) := measurableSet_singleton w
  have ht : MeasurableSet ({v} : Set (Fin n → Bool)) := measurableSet_singleton v
  have h :=
    hind.measure_inter_preimage_eq_mul (s := ({w} : Set (Fin m → Bool)))
      (t := ({v} : Set (Fin n → Bool))) hs ht
  simpa [cyl_eq_preimage, inter_assoc, inter_left_comm, inter_comm] using h

end Model

end

end FiniteDependence.MIS
