import FiniteDependence.MIS.Model

namespace FiniteDependence.MIS

open MeasureTheory Set

open scoped ProbabilityTheory

namespace Model

/-!
No stationary `k`-dependent MIS process on `ℤ` for `k ≤ 2`.

This is the short “two blocks of `00` force `11`” argument from `STATUS.md`.
-/

def w0 : Fin 1 → Bool := fun _ => false
def w1 : Fin 1 → Bool := fun _ => true

def w00 : Fin 2 → Bool := fun _ => false
def w01 : Fin 2 → Bool := fun i => decide (i.1 = 1)
def w10 : Fin 2 → Bool := fun i => decide (i.1 = 0)
def w11 : Fin 2 → Bool := fun _ => true

theorem no_stationary_kDependent_le2 (μ : Measure State) [IsProbabilityMeasure μ]
    (hstat : Stationary μ) {k : ℕ} (hk : k ≤ 2) (hdep : KDependent k μ) : False := by
  classical
  -- Let A be the `00` cylinder at positions (0,1), and B the one at positions (4,5).
  let A : Set State := cyl 0 w00
  let B : Set State := cyl 4 w00

  have hAB_empty : A ∩ B = (∅ : Set State) := by
    ext ω
    constructor
    · intro hω
      rcases hω with ⟨hA, hB⟩
      -- Extract the four forced bits and contradict `11` at (2,3).
      have h0 : ω.1 0 = false := by
        simpa [A, w00] using
          (bit_eq_of_mem_cyl (h := hA) (i := (0 : Fin 2)))
      have h1 : ω.1 1 = false := by
        simpa [A, w00] using
          (bit_eq_of_mem_cyl (h := hA) (i := (1 : Fin 2)))
      have h4 : ω.1 4 = false := by
        simpa [B, w00, add_assoc, add_left_comm, add_comm] using
          (bit_eq_of_mem_cyl (h := hB) (i := (0 : Fin 2)))
      have h5 : ω.1 5 = false := by
        simpa [B, w00, add_assoc, add_left_comm, add_comm] using
          (bit_eq_of_mem_cyl (h := hB) (i := (1 : Fin 2)))

      have h2 : ω.1 2 = true := by
        -- `00` at (0,1) forces a `1` at 2 (else `000` at 0).
        simpa [add_assoc, add_left_comm, add_comm] using twoZeros_next_true ω (i := 0) h0 h1
      have h3 : ω.1 3 = true := by
        -- `00` at (4,5) forces a `1` at 3 (else `000` at 3).
        simpa [add_assoc, add_left_comm, add_comm] using twoZeros_prev_true ω (i := 3) h4 h5

      rcases ω.2 with ⟨h11', -⟩
      have : False := by
        apply h11' 2
        exact ⟨h2, by simpa [add_assoc] using h3⟩
      simpa using this
    · intro hω
      exact False.elim (by simpa using hω)

  have hμAB : μ (A ∩ B) = 0 := by
    simpa [hAB_empty] using (measure_empty : μ (∅ : Set State) = 0)

  -- Use k-dependence (distance 3 > k) to factorize μ(A ∩ B).
  have hsepAB :
      ∀ i : Fin 2, ∀ j : Fin 2,
        Int.natAbs ((0 + Int.ofNat i.1) - (4 + Int.ofNat j.1)) > k := by
    intro i j
    fin_cases i <;> fin_cases j <;> simp
    · exact lt_of_le_of_lt hk (by decide : (2 : ℕ) < 4)
    · exact lt_of_le_of_lt hk (by decide : (2 : ℕ) < 5)
    · exact lt_of_le_of_lt hk (by decide : (2 : ℕ) < 3)
    · exact lt_of_le_of_lt hk (by decide : (2 : ℕ) < 4)

  have hμAB_fact : μ (A ∩ B) = μ A * μ B := by
    simpa [A, B] using
      (KDependent.measure_inter_cyl_eq_mul (μ := μ) (k := k) (m := 2) (n := 2) (a := 0) (b := 4)
        hdep hsepAB w00 w00)

  have hprod0 : μ A * μ B = 0 := by
    -- combine emptiness with the factorization
    simpa [hμAB_fact] using hμAB

  -- Stationarity makes μA = μB, hence μA^2 = 0.
  have hμB_eq : μ B = μ A := by
    have : μ (cyl (0 + Int.ofNat 4) w00) = μ (cyl 0 w00) :=
      Stationary.measure_cyl_add_nat (μ := μ) hstat (a := 0) (s := 4) (w := w00)
    simpa [A, B] using this

  have hμA0 : μ A = 0 := by
    have : μ A * μ A = 0 := by simpa [hμB_eq] using hprod0
    exact (mul_eq_zero.mp this).elim id id

  -- In particular, the `00` cylinder has measure 0 at positions (0,1) and also at (1,2).
  have hμ00_0 : μ (cyl 0 w00) = 0 := by simpa [A] using hμA0
  have hμ00_1 : μ (cyl 1 w00) = 0 := by
    have : μ (cyl (0 + Int.ofNat 1) w00) = μ (cyl 0 w00) :=
      Stationary.measure_cyl_add_nat (μ := μ) hstat (a := 0) (s := 1) (w := w00)
    simpa [hμ00_0] using this

  -- Let C be `{X₀ = 1}` and D be `{X₃ = 1}` (as length-1 cylinders).
  let C : Set State := cyl 0 w1
  let D : Set State := cyl 3 w1

  -- Show `C ∩ D ⊆ cyl 1 w00` (since `X₀=1` forces `X₁=0`, and `X₃=1` forces `X₂=0`).
  have hCD_sub : C ∩ D ⊆ cyl 1 w00 := by
    intro ω hω
    rcases hω with ⟨hC, hD⟩
    have h0 : ω.1 0 = true := by
      simpa [C, w1] using
        (bit_eq_of_mem_cyl (h := hC) (i := (0 : Fin 1)))
    have h3 : ω.1 3 = true := by
      simpa [D, w1, add_assoc, add_left_comm, add_comm] using
        (bit_eq_of_mem_cyl (h := hD) (i := (0 : Fin 1)))
    have h1 : ω.1 1 = false := by
      simpa [add_assoc] using true_next_false ω (i := 0) h0
    have h2 : ω.1 2 = false := by
      -- apply `true_next_false` at i=2 to rule out `X₂=1` (since `X₃=1`)
      have : ω.1 2 ≠ true := by
        rcases ω.2 with ⟨h11', -⟩
        intro h2t
        apply h11' 2
        exact ⟨h2t, by simpa [add_assoc] using h3⟩
      cases h2b : ω.1 2
      · simpa using h2b
      · exfalso
        apply this
        simpa using h2b
    -- conclude `block 1 2 ω = w00`
    have : block 1 2 ω = w00 := by
      funext j
      fin_cases j <;> simp [block, w00, h1, h2, add_assoc, add_left_comm, add_comm]
    simpa [cyl] using this

  have hμCD : μ (C ∩ D) = 0 := by
    -- monotonicity + `μ(cyl 1 w00)=0`
    exact measure_mono_null hCD_sub hμ00_1

  -- Use k-dependence to factor μ(C ∩ D).
  have hsepCD :
      ∀ i : Fin 1, ∀ j : Fin 1,
        Int.natAbs ((0 + Int.ofNat i.1) - (3 + Int.ofNat j.1)) > k := by
    intro i j
    fin_cases i <;> fin_cases j <;> simp
    exact lt_of_le_of_lt hk (by decide : (2 : ℕ) < 3)

  have hμCD_fact : μ (C ∩ D) = μ C * μ D := by
    simpa [C, D] using
      (KDependent.measure_inter_cyl_eq_mul (μ := μ) (k := k) (m := 1) (n := 1) (a := 0) (b := 3)
        hdep hsepCD w1 w1)

  -- Stationarity gives μC = μD, so μC^2 = 0, hence μC = 0.
  have hμD_eq : μ D = μ C := by
    have : μ (cyl (0 + Int.ofNat 3) w1) = μ (cyl 0 w1) :=
      Stationary.measure_cyl_add_nat (μ := μ) hstat (a := 0) (s := 3) (w := w1)
    simpa [C, D] using this

  have hμC0 : μ C = 0 := by
    have : μ C * μ C = 0 := by
      -- combine the factorization with the nullity of `C ∩ D`
      have : μ C * μ D = 0 := by simpa [hμCD_fact] using hμCD
      simpa [hμD_eq] using this
    exact (mul_eq_zero.mp this).elim id id

  -- But `μ(C)=1/2` follows from stationarity and `μ(00)=0` at positions (0,1):
  -- the three events `{00 at (0,1)}`, `{X₀=1}`, `{X₁=1}` form a partition of `univ`.
  let C1 : Set State := cyl 1 w1

  have hcover : A ∪ (C ∪ C1) = (univ : Set State) := by
    ext ω
    constructor
    · intro _
      trivial
    · intro _
      -- Split on `(X₀,X₁)`.
      cases h0 : ω.1 0
      · cases h1 : ω.1 1
        · -- 00
          left
          have : block 0 2 ω = w00 := by
            funext j
            fin_cases j <;> simp [block, w00, h0, h1]
          simpa [A, cyl] using this
        · -- 01
          right
          right
          have : block 1 1 ω = w1 := by
            funext j
            fin_cases j
            simp [block, w1, h1]
          simpa [C1, cyl] using this
      · -- 10 or 11
        right
        left
        have : block 0 1 ω = w1 := by
          funext j
          fin_cases j
          simp [block, w1, h0]
        simpa [C, cyl] using this

  have hdisjC : Disjoint C C1 := by
    refine disjoint_left.2 ?_
    intro ω hC hC1
    have h0 : ω.1 0 = true := by
      simpa [C, w1] using
        (bit_eq_of_mem_cyl (h := hC) (i := (0 : Fin 1)))
    have h1 : ω.1 1 = true := by
      simpa [C1, w1, add_assoc, add_left_comm, add_comm] using
        (bit_eq_of_mem_cyl (h := hC1) (i := (0 : Fin 1)))
    rcases ω.2 with ⟨h11', -⟩
    exact (h11' 0) ⟨h0, by simpa [add_assoc] using h1⟩

  have hdisjA : Disjoint A (C ∪ C1) := by
    refine disjoint_left.2 ?_
    intro ω hA hCU
    rcases hCU with hC | hC1
    · have h0 : ω.1 0 = false := by
        simpa [A, w00] using
          (bit_eq_of_mem_cyl (h := hA) (i := (0 : Fin 2)))
      have h0' : ω.1 0 = true := by
        simpa [C, w1] using
          (bit_eq_of_mem_cyl (h := hC) (i := (0 : Fin 1)))
      exact Bool.false_ne_true (h0.symm.trans h0')
    · have h1 : ω.1 1 = false := by
        simpa [A, w00] using
          (bit_eq_of_mem_cyl (h := hA) (i := (1 : Fin 2)))
      have h1' : ω.1 1 = true := by
        simpa [C1, w1, add_assoc, add_left_comm, add_comm] using
          (bit_eq_of_mem_cyl (h := hC1) (i := (0 : Fin 1)))
      exact Bool.false_ne_true (h1.symm.trans h1')

  have hmeasA : MeasurableSet A := by simpa [A] using (measurableSet_cyl 0 w00)
  have hmeasC : MeasurableSet C := by simpa [C] using (measurableSet_cyl 0 w1)
  have hmeasC1 : MeasurableSet C1 := by simpa [C1] using (measurableSet_cyl 1 w1)

  have hμCC1 : μ (C ∪ C1) = μ C + μ C1 := by
    simpa [union_comm, C1] using (measure_union hdisjC hmeasC1)

  have hμAC : μ (A ∪ (C ∪ C1)) = μ A + μ (C ∪ C1) := by
    have hmeasCU : MeasurableSet (C ∪ C1) := hmeasC.union hmeasC1
    simpa [union_assoc] using (measure_union hdisjA hmeasCU)

  have hμuniv : μ (univ : Set State) = 1 := by simpa using (measure_univ : μ (univ : Set State) = 1)

  have hμC1_eq : μ C1 = μ C := by
    have : μ (cyl (0 + Int.ofNat 1) w1) = μ (cyl 0 w1) :=
      Stationary.measure_cyl_add_nat (μ := μ) hstat (a := 0) (s := 1) (w := w1)
    simpa [C, C1] using this

  have : (1 : ENNReal) = 0 := by
    -- `1 = μ univ = μA + μC + μC1 = 0`
    have hμA0' : μ A = 0 := by simpa [A] using hμ00_0
    calc
      (1 : ENNReal) = μ (univ : Set State) := by simpa [hμuniv]
      _ = μ (A ∪ (C ∪ C1)) := by simpa [hcover]
      _ = μ A + μ (C ∪ C1) := hμAC
      _ = 0 + μ (C ∪ C1) := by simp [hμA0']
      _ = μ (C ∪ C1) := by simp
      _ = μ C + μ C1 := by simpa [hμCC1]
      _ = 0 + 0 := by simp [hμC0, hμC1_eq]
      _ = 0 := by simp

  exact one_ne_zero this

end Model

end FiniteDependence.MIS
