import FiniteDependence.MIS.Kernels
import FiniteDependence.MIS.K2Model
import FiniteDependence.MIS.Prob

namespace FiniteDependence.MIS

open MeasureTheory Set

open scoped ProbabilityTheory

namespace Model

noncomputable section

/-!
Bridging lemmas towards the *full* k=3 impossibility proof.

This file starts translating the combinatorial/probabilistic steps in Section 2 of
`PROOF_k_le_5.md` into Lean, on top of the abstract model in `Model.lean`.

At the moment we only formalize a first “unique completion” step (`10101` is forced by
`X₀=X₄=1`) and its probabilistic consequence.
-/

def b1 : Fin 1 → Bool := fun _ => true
def b0 : Fin 1 → Bool := fun _ => false

def w10101 : Fin 5 → Bool := fun i => decide (i.1 = 0 ∨ i.1 = 2 ∨ i.1 = 4)

def w00100 : Fin 5 → Bool := fun i => decide (i.1 = 2)
def w00101 : Fin 5 → Bool := fun i => decide (i.1 = 2 ∨ i.1 = 4)
def w01001 : Fin 5 → Bool := fun i => decide (i.1 = 1 ∨ i.1 = 4)
def w01010 : Fin 5 → Bool := fun i => decide (i.1 = 1 ∨ i.1 = 3)
def w10010 : Fin 5 → Bool := fun i => decide (i.1 = 0 ∨ i.1 = 3)
def w10100 : Fin 5 → Bool := fun i => decide (i.1 = 0 ∨ i.1 = 2)

def u0010 : Fin 4 → Bool := fun i => decide (i.1 = 2)
def u0100 : Fin 4 → Bool := fun i => decide (i.1 = 1)
def u0101 : Fin 4 → Bool := fun i => decide (i.1 = 1 ∨ i.1 = 3)
def u1001 : Fin 4 → Bool := fun i => decide (i.1 = 0 ∨ i.1 = 3)
def u1010 : Fin 4 → Bool := fun i => decide (i.1 = 0 ∨ i.1 = 2)

-- Some shorter/longer words used later in the k=3 contradiction.
def w100 : Fin 3 → Bool := fun i => decide (i.1 = 0)

def w100101 : Fin 6 → Bool := fun i => decide (i.1 = 0 ∨ i.1 = 3 ∨ i.1 = 5)
def w101001 : Fin 6 → Bool := fun i => decide (i.1 = 0 ∨ i.1 = 2 ∨ i.1 = 5)

def w10010100 : Fin 8 → Bool := fun i => decide (i.1 = 0 ∨ i.1 = 3 ∨ i.1 = 5)
def w10100100 : Fin 8 → Bool := fun i => decide (i.1 = 0 ∨ i.1 = 2 ∨ i.1 = 5)

def w010100100 : Fin 9 → Bool := fun i => decide (i.1 = 1 ∨ i.1 = 3 ∨ i.1 = 6)
def w110100100 : Fin 9 → Bool := fun i => decide (i.1 = 0 ∨ i.1 = 1 ∨ i.1 = 3 ∨ i.1 = 6)

lemma cyl10101_eq_inter :
    cyl 0 w10101 = cyl 0 b1 ∩ cyl 4 b1 := by
  ext ω
  constructor
  · intro h
    constructor
    · -- X0 = 1
      have : ω.1 0 = true := by
        simpa [w10101] using
          (bit_eq_of_mem_cyl (h := h) (i := (0 : Fin 5)))
      -- turn into length-1 cylinder at 0
      have : block 0 1 ω = b1 := by
        funext j
        fin_cases j
        simp [block, b1, this]
      simpa [cyl] using this
    · -- X4 = 1
      have : ω.1 4 = true := by
        -- in `w10101`, index 4 is `true`
        simpa [w10101] using
          (bit_eq_of_mem_cyl (h := h) (i := (4 : Fin 5)))
      have : block 4 1 ω = b1 := by
        funext j
        fin_cases j
        simp [block, b1, this]
      simpa [cyl] using this
  · rintro ⟨h0, h4⟩
    -- Extract the endpoint bits.
    have h0' : ω.1 0 = true := by
      simpa [b1] using
        (bit_eq_of_mem_cyl (h := h0) (i := (0 : Fin 1)))
    have h4' : ω.1 4 = true := by
      simpa [b1, add_assoc, add_left_comm, add_comm] using
        (bit_eq_of_mem_cyl (h := h4) (i := (0 : Fin 1)))
    -- Forced middle bits: 1 0 1 0 1.
    have h1 : ω.1 1 = false := by
      simpa [add_assoc] using true_next_false ω (i := 0) h0'
    have h3 : ω.1 3 = false := by
      -- from X4=1
      have : ω.1 3 = false := by
        simpa [add_assoc] using true_prev_false ω (i := 3) (by simpa [add_assoc] using h4')
      simpa using this
    have h2 : ω.1 2 = true := by
      -- if X2=0 then we'd have `000` at (1,2,3)
      rcases ω.2 with ⟨-, h000⟩
      have hnot : ¬(ω.1 1 = false ∧ ω.1 2 = false ∧ ω.1 3 = false) := by
        simpa [add_assoc] using h000 1
      cases h2 : ω.1 2
      · exfalso
        apply hnot
        exact ⟨h1, h2, h3⟩
      · simpa using h2
    -- Conclude the length-5 block equals `10101`.
    have : block 0 5 ω = w10101 := by
      funext j
      fin_cases j <;> simp [block, w10101, h0', h1, h2, h3, h4', add_assoc, add_left_comm, add_comm]
    simpa [cyl] using this

theorem prob_10101_eq_p2 (μ : Measure State) [IsProbabilityMeasure μ]
    (hstat : Stationary μ) (hdep : KDependent 3 μ) :
    prob μ (cyl 0 w10101) = (prob μ (cyl 0 b1)) ^ 2 := by
  have hsep :
      ∀ i : Fin 1, ∀ j : Fin 1,
        Int.natAbs ((0 + Int.ofNat i.1) - (4 + Int.ofNat j.1)) > 3 := by
    native_decide

  -- Independence gives factorization of the endpoint event.
  have hind :
      prob μ (cyl 0 b1 ∩ cyl 4 b1) = prob μ (cyl 0 b1) * prob μ (cyl 4 b1) := by
    simpa using (KDependent.prob_inter_cyl_eq_mul (μ := μ) (k := 3) (m := 1) (n := 1) (a := 0) (b := 4)
      hdep hsep b1 b1)

  -- Stationarity: P(X4=1) = P(X0=1).
  have h4 : prob μ (cyl 4 b1) = prob μ (cyl 0 b1) := by
    simpa using
      (Stationary.prob_cyl_add_nat (μ := μ) hstat (a := 0) (s := 4) (w := b1))

  -- Use the unique completion `X0=X4=1 ↔ 10101`.
  have hset : cyl 0 w10101 = cyl 0 b1 ∩ cyl 4 b1 := cyl10101_eq_inter
  -- Assemble.
  calc
    prob μ (cyl 0 w10101) = prob μ (cyl 0 b1 ∩ cyl 4 b1) := by simpa [hset]
    _ = prob μ (cyl 0 b1) * prob μ (cyl 4 b1) := hind
    _ = prob μ (cyl 0 b1) * prob μ (cyl 0 b1) := by simp [h4]
    _ = (prob μ (cyl 0 b1)) ^ 2 := by ring

/-! ### Stationarity equations for length-5 cylinders (start) -/

lemma cyl_u0010_eq_union :
    cyl 0 u0010 = cyl 0 w00100 ∪ cyl 0 w00101 := by
  ext ω
  constructor
  · intro h
    -- Extract the first 4 bits from `0010`.
    have h0 : ω.1 0 = false := by
      simpa [u0010] using
        (bit_eq_of_mem_cyl (h := h) (i := (0 : Fin 4)))
    have h1 : ω.1 1 = false := by
      simpa [u0010] using
        (bit_eq_of_mem_cyl (h := h) (i := (1 : Fin 4)))
    have h2 : ω.1 2 = true := by
      simpa [u0010] using
        (bit_eq_of_mem_cyl (h := h) (i := (2 : Fin 4)))
    have h3 : ω.1 3 = false := by
      simpa [u0010] using
        (bit_eq_of_mem_cyl (h := h) (i := (3 : Fin 4)))
    -- Case split on the 5th bit.
    cases h4 : ω.1 4
    · left
      have hw : block 0 5 ω = w00100 := by
        funext j
        fin_cases j <;> simp [block, w00100, h0, h1, h2, h3, h4]
      simpa [cyl] using hw
    · right
      have hw : block 0 5 ω = w00101 := by
        funext j
        fin_cases j <;> simp [block, w00101, h0, h1, h2, h3, h4]
      simpa [cyl] using hw
  · intro h
    rcases h with h | h
    · -- from `00100` recover `0010`
      have h0 : ω.1 0 = false := by
        simpa [w00100] using
          (bit_eq_of_mem_cyl (h := h) (i := (0 : Fin 5)))
      have h1 : ω.1 1 = false := by
        simpa [w00100] using
          (bit_eq_of_mem_cyl (h := h) (i := (1 : Fin 5)))
      have h2 : ω.1 2 = true := by
        simpa [w00100] using
          (bit_eq_of_mem_cyl (h := h) (i := (2 : Fin 5)))
      have h3 : ω.1 3 = false := by
        simpa [w00100] using
          (bit_eq_of_mem_cyl (h := h) (i := (3 : Fin 5)))
      have hu : block 0 4 ω = u0010 := by
        funext j
        fin_cases j <;> simp [block, u0010, h0, h1, h2, h3]
      simpa [cyl] using hu
    · -- from `00101` recover `0010`
      have h0 : ω.1 0 = false := by
        simpa [w00101] using
          (bit_eq_of_mem_cyl (h := h) (i := (0 : Fin 5)))
      have h1 : ω.1 1 = false := by
        simpa [w00101] using
          (bit_eq_of_mem_cyl (h := h) (i := (1 : Fin 5)))
      have h2 : ω.1 2 = true := by
        simpa [w00101] using
          (bit_eq_of_mem_cyl (h := h) (i := (2 : Fin 5)))
      have h3 : ω.1 3 = false := by
        simpa [w00101] using
          (bit_eq_of_mem_cyl (h := h) (i := (3 : Fin 5)))
      have hu : block 0 4 ω = u0010 := by
        funext j
        fin_cases j <;> simp [block, u0010, h0, h1, h2, h3]
      simpa [cyl] using hu

lemma cyl_succ_u0010_eq :
    cyl 1 u0010 = cyl 0 w10010 := by
  ext ω
  constructor
  · intro h
    -- Extract bits at 1..4.
    have h1 : ω.1 1 = false := by
      simpa [u0010, add_assoc, add_left_comm, add_comm] using
        (bit_eq_of_mem_cyl (h := h) (i := (0 : Fin 4)))
    have h2 : ω.1 2 = false := by
      simpa [u0010, add_assoc, add_left_comm, add_comm] using
        (bit_eq_of_mem_cyl (h := h) (i := (1 : Fin 4)))
    have h3 : ω.1 3 = true := by
      simpa [u0010, add_assoc, add_left_comm, add_comm] using
        (bit_eq_of_mem_cyl (h := h) (i := (2 : Fin 4)))
    have h4 : ω.1 4 = false := by
      simpa [u0010, add_assoc, add_left_comm, add_comm] using
        (bit_eq_of_mem_cyl (h := h) (i := (3 : Fin 4)))
    -- Force X0 = 1 from `00` at (1,2).
    have h0 : ω.1 0 = true := by
      simpa [add_assoc] using twoZeros_prev_true ω (i := 0) h1 h2
    have hw : block 0 5 ω = w10010 := by
      funext j
      fin_cases j <;> simp [block, w10010, h0, h1, h2, h3, h4, add_assoc, add_left_comm, add_comm]
    simpa [cyl] using hw
  · intro h
    -- from `10010` recover the suffix `0010`
    have h1 : ω.1 1 = false := by
      simpa [w10010] using
        (bit_eq_of_mem_cyl (h := h) (i := (1 : Fin 5)))
    have h2 : ω.1 2 = false := by
      simpa [w10010] using
        (bit_eq_of_mem_cyl (h := h) (i := (2 : Fin 5)))
    have h3 : ω.1 3 = true := by
      simpa [w10010] using
        (bit_eq_of_mem_cyl (h := h) (i := (3 : Fin 5)))
    have h4 : ω.1 4 = false := by
      simpa [w10010] using
        (bit_eq_of_mem_cyl (h := h) (i := (4 : Fin 5)))
    have hu : block 1 4 ω = u0010 := by
      funext j
      fin_cases j <;> simp [block, u0010, h1, h2, h3, h4, add_assoc, add_left_comm, add_comm]
    simpa [cyl] using hu

theorem prob_eq_u0010 (μ : Measure State) [IsProbabilityMeasure μ] (hstat : Stationary μ) :
    prob μ (cyl 0 w00100) + prob μ (cyl 0 w00101) = prob μ (cyl 0 w10010) := by
  -- Stationarity at length 4: `P(block₀..₃ = 0010) = P(block₁..₄ = 0010)`.
  have hstat4 : prob μ (cyl 1 u0010) = prob μ (cyl 0 u0010) :=
    Stationary.prob_cyl_succ (μ := μ) hstat (a := 0) (w := u0010)

  -- Rewrite both sides using the cylinder identities above.
  have hL : prob μ (cyl 0 u0010) = prob μ (cyl 0 w00100 ∪ cyl 0 w00101) := by
    simpa [cyl_u0010_eq_union] using (rfl : prob μ (cyl 0 u0010) = prob μ (cyl 0 u0010))
  have hR : prob μ (cyl 1 u0010) = prob μ (cyl 0 w10010) := by
    simpa [cyl_succ_u0010_eq] using (rfl : prob μ (cyl 1 u0010) = prob μ (cyl 1 u0010))

  have hmain : prob μ (cyl 0 w00100 ∪ cyl 0 w00101) = prob μ (cyl 0 w10010) := by
    -- combine stationarity with the rewrites
    calc
      prob μ (cyl 0 w00100 ∪ cyl 0 w00101) = prob μ (cyl 0 u0010) := by simpa [hL]
      _ = prob μ (cyl 1 u0010) := by simpa using hstat4.symm
      _ = prob μ (cyl 0 w10010) := by simpa [hR]

  -- Expand the union probability as a sum (disjoint union).
  have hne : w00100 ≠ w00101 := by
    native_decide
  have hunion : prob μ (cyl 0 w00100 ∪ cyl 0 w00101) =
      prob μ (cyl 0 w00100) + prob μ (cyl 0 w00101) :=
    prob_union_cyl_of_ne (μ := μ) (a := 0) hne
  -- Finish.
  simpa [hunion] using hmain

lemma cyl_u0100_eq : cyl 0 u0100 = cyl 0 w01001 := by
  ext ω
  constructor
  · intro h
    -- Extract the first 4 bits `0100`.
    have h0 : ω.1 0 = false := by
      simpa [u0100] using
        (bit_eq_of_mem_cyl (h := h) (i := (0 : Fin 4)))
    have h1 : ω.1 1 = true := by
      simpa [u0100] using
        (bit_eq_of_mem_cyl (h := h) (i := (1 : Fin 4)))
    have h2 : ω.1 2 = false := by
      simpa [u0100] using
        (bit_eq_of_mem_cyl (h := h) (i := (2 : Fin 4)))
    have h3 : ω.1 3 = false := by
      simpa [u0100] using
        (bit_eq_of_mem_cyl (h := h) (i := (3 : Fin 4)))
    -- Force the last bit to be 1 from `00` at (2,3).
    have h4 : ω.1 4 = true := by
      simpa [add_assoc] using twoZeros_next_true ω (i := 2) h2 h3
    have hw : block 0 5 ω = w01001 := by
      funext j
      fin_cases j <;> simp [block, w01001, h0, h1, h2, h3, h4]
    simpa [cyl] using hw
  · intro h
    -- from `01001` recover prefix `0100`
    have h0 : ω.1 0 = false := by
      simpa [w01001] using
        (bit_eq_of_mem_cyl (h := h) (i := (0 : Fin 5)))
    have h1 : ω.1 1 = true := by
      simpa [w01001] using
        (bit_eq_of_mem_cyl (h := h) (i := (1 : Fin 5)))
    have h2 : ω.1 2 = false := by
      simpa [w01001] using
        (bit_eq_of_mem_cyl (h := h) (i := (2 : Fin 5)))
    have h3 : ω.1 3 = false := by
      simpa [w01001] using
        (bit_eq_of_mem_cyl (h := h) (i := (3 : Fin 5)))
    have hu : block 0 4 ω = u0100 := by
      funext j
      fin_cases j <;> simp [block, u0100, h0, h1, h2, h3]
    simpa [cyl] using hu

lemma cyl_succ_u0100_eq_union :
    cyl 1 u0100 = cyl 0 w00100 ∪ cyl 0 w10100 := by
  ext ω
  constructor
  · intro h
    -- Extract bits at 1..4: `0100`.
    have h1 : ω.1 1 = false := by
      simpa [u0100, add_assoc, add_left_comm, add_comm] using
        (bit_eq_of_mem_cyl (h := h) (i := (0 : Fin 4)))
    have h2 : ω.1 2 = true := by
      simpa [u0100, add_assoc, add_left_comm, add_comm] using
        (bit_eq_of_mem_cyl (h := h) (i := (1 : Fin 4)))
    have h3 : ω.1 3 = false := by
      simpa [u0100, add_assoc, add_left_comm, add_comm] using
        (bit_eq_of_mem_cyl (h := h) (i := (2 : Fin 4)))
    have h4 : ω.1 4 = false := by
      simpa [u0100, add_assoc, add_left_comm, add_comm] using
        (bit_eq_of_mem_cyl (h := h) (i := (3 : Fin 4)))
    -- Case split on X0.
    cases h0 : ω.1 0
    · left
      have hw : block 0 5 ω = w00100 := by
        funext j
        fin_cases j <;> simp [block, w00100, h0, h1, h2, h3, h4]
      simpa [cyl] using hw
    · right
      have hw : block 0 5 ω = w10100 := by
        funext j
        fin_cases j <;> simp [block, w10100, h0, h1, h2, h3, h4]
      simpa [cyl] using hw
  · intro h
    rcases h with h | h
    · -- from `00100` recover suffix `0100`
      have h1 : ω.1 1 = false := by
        simpa [w00100] using
          (bit_eq_of_mem_cyl (h := h) (i := (1 : Fin 5)))
      have h2 : ω.1 2 = true := by
        simpa [w00100] using
          (bit_eq_of_mem_cyl (h := h) (i := (2 : Fin 5)))
      have h3 : ω.1 3 = false := by
        simpa [w00100] using
          (bit_eq_of_mem_cyl (h := h) (i := (3 : Fin 5)))
      have h4 : ω.1 4 = false := by
        simpa [w00100] using
          (bit_eq_of_mem_cyl (h := h) (i := (4 : Fin 5)))
      have hu : block 1 4 ω = u0100 := by
        funext j
        fin_cases j <;> simp [block, u0100, h1, h2, h3, h4, add_assoc, add_left_comm, add_comm]
      simpa [cyl] using hu
    · -- from `10100` recover suffix `0100`
      have h1 : ω.1 1 = false := by
        simpa [w10100] using
          (bit_eq_of_mem_cyl (h := h) (i := (1 : Fin 5)))
      have h2 : ω.1 2 = true := by
        simpa [w10100] using
          (bit_eq_of_mem_cyl (h := h) (i := (2 : Fin 5)))
      have h3 : ω.1 3 = false := by
        simpa [w10100] using
          (bit_eq_of_mem_cyl (h := h) (i := (3 : Fin 5)))
      have h4 : ω.1 4 = false := by
        simpa [w10100] using
          (bit_eq_of_mem_cyl (h := h) (i := (4 : Fin 5)))
      have hu : block 1 4 ω = u0100 := by
        funext j
        fin_cases j <;> simp [block, u0100, h1, h2, h3, h4, add_assoc, add_left_comm, add_comm]
      simpa [cyl] using hu

theorem prob_eq_u0100 (μ : Measure State) [IsProbabilityMeasure μ] (hstat : Stationary μ) :
    prob μ (cyl 0 w01001) = prob μ (cyl 0 w00100) + prob μ (cyl 0 w10100) := by
  have hstat4 : prob μ (cyl 1 u0100) = prob μ (cyl 0 u0100) :=
    Stationary.prob_cyl_succ (μ := μ) hstat (a := 0) (w := u0100)
  -- Rewrite and expand the union.
  have hmain : prob μ (cyl 0 w01001) = prob μ (cyl 0 w00100 ∪ cyl 0 w10100) := by
    calc
      prob μ (cyl 0 w01001) = prob μ (cyl 0 u0100) := by simpa [cyl_u0100_eq]
      _ = prob μ (cyl 1 u0100) := by simpa using hstat4.symm
      _ = prob μ (cyl 0 w00100 ∪ cyl 0 w10100) := by simpa [cyl_succ_u0100_eq_union]
  have hne : w00100 ≠ w10100 := by
    native_decide
  have hunion : prob μ (cyl 0 w00100 ∪ cyl 0 w10100) =
      prob μ (cyl 0 w00100) + prob μ (cyl 0 w10100) :=
    prob_union_cyl_of_ne (μ := μ) (a := 0) hne
  simpa [hunion] using hmain

lemma cyl_u0101_eq : cyl 0 u0101 = cyl 0 w01010 := by
  ext ω
  constructor
  · intro h
    -- Extract the prefix `0101`.
    have h0 : ω.1 0 = false := by
      simpa [u0101] using
        (bit_eq_of_mem_cyl (h := h) (i := (0 : Fin 4)))
    have h1 : ω.1 1 = true := by
      simpa [u0101] using
        (bit_eq_of_mem_cyl (h := h) (i := (1 : Fin 4)))
    have h2 : ω.1 2 = false := by
      simpa [u0101] using
        (bit_eq_of_mem_cyl (h := h) (i := (2 : Fin 4)))
    have h3 : ω.1 3 = true := by
      simpa [u0101] using
        (bit_eq_of_mem_cyl (h := h) (i := (3 : Fin 4)))
    -- Last bit forced to 0 (no `11` at (3,4)).
    have h4 : ω.1 4 = false := by
      simpa [add_assoc] using true_next_false ω (i := 3) (by simpa [add_assoc] using h3)
    have hw : block 0 5 ω = w01010 := by
      funext j
      fin_cases j <;> simp [block, w01010, h0, h1, h2, h3, h4]
    simpa [cyl] using hw
  · intro h
    -- from `01010` recover prefix `0101`
    have h0 : ω.1 0 = false := by
      simpa [w01010] using
        (bit_eq_of_mem_cyl (h := h) (i := (0 : Fin 5)))
    have h1 : ω.1 1 = true := by
      simpa [w01010] using
        (bit_eq_of_mem_cyl (h := h) (i := (1 : Fin 5)))
    have h2 : ω.1 2 = false := by
      simpa [w01010] using
        (bit_eq_of_mem_cyl (h := h) (i := (2 : Fin 5)))
    have h3 : ω.1 3 = true := by
      simpa [w01010] using
        (bit_eq_of_mem_cyl (h := h) (i := (3 : Fin 5)))
    have hu : block 0 4 ω = u0101 := by
      funext j
      fin_cases j <;> simp [block, u0101, h0, h1, h2, h3]
    simpa [cyl] using hu

lemma cyl_succ_u0101_eq_union :
    cyl 1 u0101 = cyl 0 w00101 ∪ cyl 0 w10101 := by
  ext ω
  constructor
  · intro h
    -- Extract bits at 1..4: `0101`.
    have h1 : ω.1 1 = false := by
      simpa [u0101, add_assoc, add_left_comm, add_comm] using
        (bit_eq_of_mem_cyl (h := h) (i := (0 : Fin 4)))
    have h2 : ω.1 2 = true := by
      simpa [u0101, add_assoc, add_left_comm, add_comm] using
        (bit_eq_of_mem_cyl (h := h) (i := (1 : Fin 4)))
    have h3 : ω.1 3 = false := by
      simpa [u0101, add_assoc, add_left_comm, add_comm] using
        (bit_eq_of_mem_cyl (h := h) (i := (2 : Fin 4)))
    have h4 : ω.1 4 = true := by
      simpa [u0101, add_assoc, add_left_comm, add_comm] using
        (bit_eq_of_mem_cyl (h := h) (i := (3 : Fin 4)))
    cases h0 : ω.1 0
    · left
      have hw : block 0 5 ω = w00101 := by
        funext j
        fin_cases j <;> simp [block, w00101, h0, h1, h2, h3, h4]
      simpa [cyl] using hw
    · right
      have hw : block 0 5 ω = w10101 := by
        funext j
        fin_cases j <;> simp [block, w10101, h0, h1, h2, h3, h4]
      simpa [cyl] using hw
  · intro h
    rcases h with h | h
    · -- `00101` has suffix `0101`
      have h1 : ω.1 1 = false := by
        simpa [w00101] using
          (bit_eq_of_mem_cyl (h := h) (i := (1 : Fin 5)))
      have h2 : ω.1 2 = true := by
        simpa [w00101] using
          (bit_eq_of_mem_cyl (h := h) (i := (2 : Fin 5)))
      have h3 : ω.1 3 = false := by
        simpa [w00101] using
          (bit_eq_of_mem_cyl (h := h) (i := (3 : Fin 5)))
      have h4 : ω.1 4 = true := by
        simpa [w00101] using
          (bit_eq_of_mem_cyl (h := h) (i := (4 : Fin 5)))
      have hu : block 1 4 ω = u0101 := by
        funext j
        fin_cases j <;> simp [block, u0101, h1, h2, h3, h4, add_assoc, add_left_comm, add_comm]
      simpa [cyl] using hu
    · -- `10101` has suffix `0101`
      have h1 : ω.1 1 = false := by
        simpa [w10101] using
          (bit_eq_of_mem_cyl (h := h) (i := (1 : Fin 5)))
      have h2 : ω.1 2 = true := by
        simpa [w10101] using
          (bit_eq_of_mem_cyl (h := h) (i := (2 : Fin 5)))
      have h3 : ω.1 3 = false := by
        simpa [w10101] using
          (bit_eq_of_mem_cyl (h := h) (i := (3 : Fin 5)))
      have h4 : ω.1 4 = true := by
        simpa [w10101] using
          (bit_eq_of_mem_cyl (h := h) (i := (4 : Fin 5)))
      have hu : block 1 4 ω = u0101 := by
        funext j
        fin_cases j <;> simp [block, u0101, h1, h2, h3, h4, add_assoc, add_left_comm, add_comm]
      simpa [cyl] using hu

theorem prob_eq_u0101 (μ : Measure State) [IsProbabilityMeasure μ] (hstat : Stationary μ) :
    prob μ (cyl 0 w01010) = prob μ (cyl 0 w00101) + prob μ (cyl 0 w10101) := by
  have hstat4 : prob μ (cyl 1 u0101) = prob μ (cyl 0 u0101) :=
    Stationary.prob_cyl_succ (μ := μ) hstat (a := 0) (w := u0101)
  have hmain : prob μ (cyl 0 w01010) = prob μ (cyl 0 w00101 ∪ cyl 0 w10101) := by
    calc
      prob μ (cyl 0 w01010) = prob μ (cyl 0 u0101) := by simpa [cyl_u0101_eq]
      _ = prob μ (cyl 1 u0101) := by simpa using hstat4.symm
      _ = prob μ (cyl 0 w00101 ∪ cyl 0 w10101) := by simpa [cyl_succ_u0101_eq_union]
  have hne : w00101 ≠ w10101 := by
    native_decide
  have hunion : prob μ (cyl 0 w00101 ∪ cyl 0 w10101) =
      prob μ (cyl 0 w00101) + prob μ (cyl 0 w10101) :=
    prob_union_cyl_of_ne (μ := μ) (a := 0) hne
  simpa [hunion] using hmain

lemma cyl_u1001_eq : cyl 0 u1001 = cyl 0 w10010 := by
  ext ω
  constructor
  · intro h
    -- Extract prefix `1001`.
    have h0 : ω.1 0 = true := by
      simpa [u1001] using
        (bit_eq_of_mem_cyl (h := h) (i := (0 : Fin 4)))
    have h1 : ω.1 1 = false := by
      simpa [u1001] using
        (bit_eq_of_mem_cyl (h := h) (i := (1 : Fin 4)))
    have h2 : ω.1 2 = false := by
      simpa [u1001] using
        (bit_eq_of_mem_cyl (h := h) (i := (2 : Fin 4)))
    have h3 : ω.1 3 = true := by
      simpa [u1001] using
        (bit_eq_of_mem_cyl (h := h) (i := (3 : Fin 4)))
    have h4 : ω.1 4 = false := by
      simpa [add_assoc] using true_next_false ω (i := 3) (by simpa [add_assoc] using h3)
    have hw : block 0 5 ω = w10010 := by
      funext j
      fin_cases j <;> simp [block, w10010, h0, h1, h2, h3, h4]
    simpa [cyl] using hw
  · intro h
    -- from `10010` recover prefix `1001`
    have h0 : ω.1 0 = true := by
      simpa [w10010] using
        (bit_eq_of_mem_cyl (h := h) (i := (0 : Fin 5)))
    have h1 : ω.1 1 = false := by
      simpa [w10010] using
        (bit_eq_of_mem_cyl (h := h) (i := (1 : Fin 5)))
    have h2 : ω.1 2 = false := by
      simpa [w10010] using
        (bit_eq_of_mem_cyl (h := h) (i := (2 : Fin 5)))
    have h3 : ω.1 3 = true := by
      simpa [w10010] using
        (bit_eq_of_mem_cyl (h := h) (i := (3 : Fin 5)))
    have hu : block 0 4 ω = u1001 := by
      funext j
      fin_cases j <;> simp [block, u1001, h0, h1, h2, h3]
    simpa [cyl] using hu

lemma cyl_succ_u1001_eq : cyl 1 u1001 = cyl 0 w01001 := by
  ext ω
  constructor
  · intro h
    -- Extract bits at 1..4: `1001`.
    have h1 : ω.1 1 = true := by
      simpa [u1001, add_assoc, add_left_comm, add_comm] using
        (bit_eq_of_mem_cyl (h := h) (i := (0 : Fin 4)))
    have h2 : ω.1 2 = false := by
      simpa [u1001, add_assoc, add_left_comm, add_comm] using
        (bit_eq_of_mem_cyl (h := h) (i := (1 : Fin 4)))
    have h3 : ω.1 3 = false := by
      simpa [u1001, add_assoc, add_left_comm, add_comm] using
        (bit_eq_of_mem_cyl (h := h) (i := (2 : Fin 4)))
    have h4 : ω.1 4 = true := by
      simpa [u1001, add_assoc, add_left_comm, add_comm] using
        (bit_eq_of_mem_cyl (h := h) (i := (3 : Fin 4)))
    -- Force X0=0 (since X1=1).
    have h0 : ω.1 0 = false := by
      simpa [add_assoc] using true_prev_false ω (i := 0) (by simpa [add_assoc] using h1)
    have hw : block 0 5 ω = w01001 := by
      funext j
      fin_cases j <;> simp [block, w01001, h0, h1, h2, h3, h4]
    simpa [cyl] using hw
  · intro h
    -- from `01001` recover suffix `1001`
    have h1 : ω.1 1 = true := by
      simpa [w01001] using
        (bit_eq_of_mem_cyl (h := h) (i := (1 : Fin 5)))
    have h2 : ω.1 2 = false := by
      simpa [w01001] using
        (bit_eq_of_mem_cyl (h := h) (i := (2 : Fin 5)))
    have h3 : ω.1 3 = false := by
      simpa [w01001] using
        (bit_eq_of_mem_cyl (h := h) (i := (3 : Fin 5)))
    have h4 : ω.1 4 = true := by
      simpa [w01001] using
        (bit_eq_of_mem_cyl (h := h) (i := (4 : Fin 5)))
    have hu : block 1 4 ω = u1001 := by
      funext j
      fin_cases j <;> simp [block, u1001, h1, h2, h3, h4, add_assoc, add_left_comm, add_comm]
    simpa [cyl] using hu

theorem prob_eq_u1001 (μ : Measure State) [IsProbabilityMeasure μ] (hstat : Stationary μ) :
    prob μ (cyl 0 w10010) = prob μ (cyl 0 w01001) := by
  have hstat4 : prob μ (cyl 1 u1001) = prob μ (cyl 0 u1001) :=
    Stationary.prob_cyl_succ (μ := μ) hstat (a := 0) (w := u1001)
  calc
    prob μ (cyl 0 w10010) = prob μ (cyl 0 u1001) := by simpa [cyl_u1001_eq]
    _ = prob μ (cyl 1 u1001) := by simpa using hstat4.symm
    _ = prob μ (cyl 0 w01001) := by simpa [cyl_succ_u1001_eq]

lemma cyl_u1010_eq_union : cyl 0 u1010 = cyl 0 w10100 ∪ cyl 0 w10101 := by
  ext ω
  constructor
  · intro h
    -- Extract prefix `1010`.
    have h0 : ω.1 0 = true := by
      simpa [u1010] using
        (bit_eq_of_mem_cyl (h := h) (i := (0 : Fin 4)))
    have h1 : ω.1 1 = false := by
      simpa [u1010] using
        (bit_eq_of_mem_cyl (h := h) (i := (1 : Fin 4)))
    have h2 : ω.1 2 = true := by
      simpa [u1010] using
        (bit_eq_of_mem_cyl (h := h) (i := (2 : Fin 4)))
    have h3 : ω.1 3 = false := by
      simpa [u1010] using
        (bit_eq_of_mem_cyl (h := h) (i := (3 : Fin 4)))
    cases h4 : ω.1 4
    · left
      have hw : block 0 5 ω = w10100 := by
        funext j
        fin_cases j <;> simp [block, w10100, h0, h1, h2, h3, h4]
      simpa [cyl] using hw
    · right
      have hw : block 0 5 ω = w10101 := by
        funext j
        fin_cases j <;> simp [block, w10101, h0, h1, h2, h3, h4]
      simpa [cyl] using hw
  · intro h
    rcases h with h | h
    · -- from `10100` recover prefix `1010`
      have h0 : ω.1 0 = true := by
        simpa [w10100] using
          (bit_eq_of_mem_cyl (h := h) (i := (0 : Fin 5)))
      have h1 : ω.1 1 = false := by
        simpa [w10100] using
          (bit_eq_of_mem_cyl (h := h) (i := (1 : Fin 5)))
      have h2 : ω.1 2 = true := by
        simpa [w10100] using
          (bit_eq_of_mem_cyl (h := h) (i := (2 : Fin 5)))
      have h3 : ω.1 3 = false := by
        simpa [w10100] using
          (bit_eq_of_mem_cyl (h := h) (i := (3 : Fin 5)))
      have hu : block 0 4 ω = u1010 := by
        funext j
        fin_cases j <;> simp [block, u1010, h0, h1, h2, h3]
      simpa [cyl] using hu
    · -- from `10101` recover prefix `1010`
      have h0 : ω.1 0 = true := by
        simpa [w10101] using
          (bit_eq_of_mem_cyl (h := h) (i := (0 : Fin 5)))
      have h1 : ω.1 1 = false := by
        simpa [w10101] using
          (bit_eq_of_mem_cyl (h := h) (i := (1 : Fin 5)))
      have h2 : ω.1 2 = true := by
        simpa [w10101] using
          (bit_eq_of_mem_cyl (h := h) (i := (2 : Fin 5)))
      have h3 : ω.1 3 = false := by
        simpa [w10101] using
          (bit_eq_of_mem_cyl (h := h) (i := (3 : Fin 5)))
      have hu : block 0 4 ω = u1010 := by
        funext j
        fin_cases j <;> simp [block, u1010, h0, h1, h2, h3]
      simpa [cyl] using hu

lemma cyl_succ_u1010_eq : cyl 1 u1010 = cyl 0 w01010 := by
  ext ω
  constructor
  · intro h
    -- Extract suffix `1010` at 1..4.
    have h1 : ω.1 1 = true := by
      simpa [u1010, add_assoc, add_left_comm, add_comm] using
        (bit_eq_of_mem_cyl (h := h) (i := (0 : Fin 4)))
    have h2 : ω.1 2 = false := by
      simpa [u1010, add_assoc, add_left_comm, add_comm] using
        (bit_eq_of_mem_cyl (h := h) (i := (1 : Fin 4)))
    have h3 : ω.1 3 = true := by
      simpa [u1010, add_assoc, add_left_comm, add_comm] using
        (bit_eq_of_mem_cyl (h := h) (i := (2 : Fin 4)))
    have h4 : ω.1 4 = false := by
      simpa [u1010, add_assoc, add_left_comm, add_comm] using
        (bit_eq_of_mem_cyl (h := h) (i := (3 : Fin 4)))
    -- Force X0=0 since X1=1.
    have h0 : ω.1 0 = false := by
      simpa [add_assoc] using true_prev_false ω (i := 0) (by simpa [add_assoc] using h1)
    have hw : block 0 5 ω = w01010 := by
      funext j
      fin_cases j <;> simp [block, w01010, h0, h1, h2, h3, h4]
    simpa [cyl] using hw
  · intro h
    -- from `01010` recover suffix `1010`
    have h1 : ω.1 1 = true := by
      simpa [w01010] using
        (bit_eq_of_mem_cyl (h := h) (i := (1 : Fin 5)))
    have h2 : ω.1 2 = false := by
      simpa [w01010] using
        (bit_eq_of_mem_cyl (h := h) (i := (2 : Fin 5)))
    have h3 : ω.1 3 = true := by
      simpa [w01010] using
        (bit_eq_of_mem_cyl (h := h) (i := (3 : Fin 5)))
    have h4 : ω.1 4 = false := by
      simpa [w01010] using
        (bit_eq_of_mem_cyl (h := h) (i := (4 : Fin 5)))
    have hu : block 1 4 ω = u1010 := by
      funext j
      fin_cases j <;> simp [block, u1010, h1, h2, h3, h4, add_assoc, add_left_comm, add_comm]
    simpa [cyl] using hu

theorem prob_eq_u1010 (μ : Measure State) [IsProbabilityMeasure μ] (hstat : Stationary μ) :
    prob μ (cyl 0 w10100) + prob μ (cyl 0 w10101) = prob μ (cyl 0 w01010) := by
  have hstat4 : prob μ (cyl 1 u1010) = prob μ (cyl 0 u1010) :=
    Stationary.prob_cyl_succ (μ := μ) hstat (a := 0) (w := u1010)
  have hmain : prob μ (cyl 0 w10100 ∪ cyl 0 w10101) = prob μ (cyl 0 w01010) := by
    calc
      prob μ (cyl 0 w10100 ∪ cyl 0 w10101) = prob μ (cyl 0 u1010) := by
        simpa [cyl_u1010_eq_union]
      _ = prob μ (cyl 1 u1010) := by simpa using hstat4.symm
      _ = prob μ (cyl 0 w01010) := by simpa [cyl_succ_u1010_eq]
  have hne : w10100 ≠ w10101 := by
    native_decide
  have hunion : prob μ (cyl 0 w10100 ∪ cyl 0 w10101) =
      prob μ (cyl 0 w10100) + prob μ (cyl 0 w10101) :=
    prob_union_cyl_of_ne (μ := μ) (a := 0) hne
  simpa [hunion] using hmain

/-! ### Endpoint constraints from 3-dependence at distance 4 -/

lemma endpoints00_eq_union :
    cyl 0 b0 ∩ cyl 4 b0 = cyl 0 w00100 ∪ cyl 0 w01010 := by
  ext ω
  constructor
  · rintro ⟨h0, h4⟩
    have h0' : ω.1 0 = false := by
      simpa [b0] using
        (bit_eq_of_mem_cyl (h := h0) (i := (0 : Fin 1)))
    have h4' : ω.1 4 = false := by
      simpa [b0, add_assoc, add_left_comm, add_comm] using
        (bit_eq_of_mem_cyl (h := h4) (i := (0 : Fin 1)))
    -- Split on X1.
    cases h1 : ω.1 1
    · left
      -- X1=0 forces X2=1, hence X3=0 (since X4=0).
      have h2 : ω.1 2 = true := by
        simpa [add_assoc] using twoZeros_next_true ω (i := 0) h0' h1
      have h3 : ω.1 3 = false := by
        simpa [add_assoc] using true_next_false ω (i := 2) (by simpa [add_assoc] using h2)
      have hw : block 0 5 ω = w00100 := by
        funext j
        fin_cases j <;> simp [block, w00100, h0', h1, h2, h3, h4']
      simpa [cyl] using hw
    · right
      -- X1=1 forces X2=0 and then X3=1 (else 000 at 2..4).
      have h2 : ω.1 2 = false := by
        simpa [add_assoc] using true_next_false ω (i := 1) (by simpa [add_assoc] using h1)
      have h3 : ω.1 3 = true := by
        -- if X3=0 then we'd have `000` at (2,3,4)
        rcases ω.2 with ⟨-, h000⟩
        have hnot : ¬(ω.1 2 = false ∧ ω.1 3 = false ∧ ω.1 4 = false) := by
          simpa [add_assoc] using h000 2
        cases h3 : ω.1 3
        · exfalso
          exact hnot ⟨h2, h3, h4'⟩
        · simpa using h3
      have hw : block 0 5 ω = w01010 := by
        funext j
        fin_cases j <;> simp [block, w01010, h0', h1, h2, h3, h4']
      simpa [cyl] using hw
  · intro h
    rcases h with h | h
    · -- `00100` has endpoints 0,0
      constructor
      · have : ω.1 0 = false := by
          simpa [w00100] using
            (bit_eq_of_mem_cyl (h := h) (i := (0 : Fin 5)))
        have hb : block 0 1 ω = b0 := by
          funext j; fin_cases j; simp [block, b0, this]
        simpa [cyl] using hb
      · have : ω.1 4 = false := by
          simpa [w00100] using
            (bit_eq_of_mem_cyl (h := h) (i := (4 : Fin 5)))
        have hb : block 4 1 ω = b0 := by
          funext j; fin_cases j; simp [block, b0, this]
        simpa [cyl] using hb
    · -- `01010` has endpoints 0,0
      constructor
      · have : ω.1 0 = false := by
          simpa [w01010] using
            (bit_eq_of_mem_cyl (h := h) (i := (0 : Fin 5)))
        have hb : block 0 1 ω = b0 := by
          funext j; fin_cases j; simp [block, b0, this]
        simpa [cyl] using hb
      · have : ω.1 4 = false := by
          simpa [w01010] using
            (bit_eq_of_mem_cyl (h := h) (i := (4 : Fin 5)))
        have hb : block 4 1 ω = b0 := by
          funext j; fin_cases j; simp [block, b0, this]
        simpa [cyl] using hb

lemma endpoints10_eq_union :
    cyl 0 b1 ∩ cyl 4 b0 = cyl 0 w10010 ∪ cyl 0 w10100 := by
  ext ω
  constructor
  · rintro ⟨h0, h4⟩
    have h0' : ω.1 0 = true := by
      simpa [b1] using
        (bit_eq_of_mem_cyl (h := h0) (i := (0 : Fin 1)))
    have h4' : ω.1 4 = false := by
      simpa [b0, add_assoc, add_left_comm, add_comm] using
        (bit_eq_of_mem_cyl (h := h4) (i := (0 : Fin 1)))
    -- X0=1 forces X1=0.
    have h1 : ω.1 1 = false := by
      simpa [add_assoc] using true_next_false ω (i := 0) h0'
    -- Split on X2.
    cases h2 : ω.1 2
    · left
      -- Then `00` at (1,2) forces X3=1.
      have h3 : ω.1 3 = true := by
        simpa [add_assoc] using twoZeros_next_true ω (i := 1) h1 h2
      have hw : block 0 5 ω = w10010 := by
        funext j
        fin_cases j <;> simp [block, w10010, h0', h1, h2, h3, h4']
      simpa [cyl] using hw
    · right
      -- Then X3=0 and the word is `10100`.
      have h3 : ω.1 3 = false := by
        simpa [add_assoc] using true_next_false ω (i := 2) (by simpa using h2)
      have hw : block 0 5 ω = w10100 := by
        funext j
        fin_cases j <;> simp [block, w10100, h0', h1, h2, h3, h4']
      simpa [cyl] using hw
  · intro h
    rcases h with h | h
    · constructor
      · have : ω.1 0 = true := by
          simpa [w10010] using
            (bit_eq_of_mem_cyl (h := h) (i := (0 : Fin 5)))
        have hb : block 0 1 ω = b1 := by
          funext j; fin_cases j; simp [block, b1, this]
        simpa [cyl] using hb
      · have : ω.1 4 = false := by
          simpa [w10010] using
            (bit_eq_of_mem_cyl (h := h) (i := (4 : Fin 5)))
        have hb : block 4 1 ω = b0 := by
          funext j; fin_cases j; simp [block, b0, this]
        simpa [cyl] using hb
    · constructor
      · have : ω.1 0 = true := by
          simpa [w10100] using
            (bit_eq_of_mem_cyl (h := h) (i := (0 : Fin 5)))
        have hb : block 0 1 ω = b1 := by
          funext j; fin_cases j; simp [block, b1, this]
        simpa [cyl] using hb
      · have : ω.1 4 = false := by
          simpa [w10100] using
            (bit_eq_of_mem_cyl (h := h) (i := (4 : Fin 5)))
        have hb : block 4 1 ω = b0 := by
          funext j; fin_cases j; simp [block, b0, this]
        simpa [cyl] using hb

theorem prob_b0 (μ : Measure State) [IsProbabilityMeasure μ] :
    prob μ (cyl 0 b0) = 1 - prob μ (cyl 0 b1) := by
  -- `X₀` is either 0 or 1.
  have hcover : cyl 0 b0 ∪ cyl 0 b1 = (univ : Set State) := by
    ext ω
    constructor
    · intro _
      trivial
    · intro _
      cases h0 : ω.1 0
      · left
        have hb : block 0 1 ω = b0 := by
          funext j
          fin_cases j
          simp [block, b0, h0]
        simpa [cyl] using hb
      · right
        have hb : block 0 1 ω = b1 := by
          funext j
          fin_cases j
          simp [block, b1, h0]
        simpa [cyl] using hb
  have hne : b0 ≠ b1 := by
    native_decide
  have hunion : prob μ (cyl 0 b0 ∪ cyl 0 b1) = prob μ (cyl 0 b0) + prob μ (cyl 0 b1) :=
    prob_union_cyl_of_ne (μ := μ) (a := 0) hne
  have : (1 : ℝ) = prob μ (cyl 0 b0) + prob μ (cyl 0 b1) := by
    -- rewrite LHS as `prob μ univ`
    simpa [prob_univ (μ := μ), hcover] using hunion.trans (by rfl)
  linarith

theorem prob_endpoints00 (μ : Measure State) [IsProbabilityMeasure μ]
    (hstat : Stationary μ) (hdep : KDependent 3 μ) :
    prob μ (cyl 0 w00100) + prob μ (cyl 0 w01010) =
      (1 - prob μ (cyl 0 b1)) ^ 2 := by
  classical
  -- independence between X0 and X4 (distance 4 > 3)
  have hsep :
      ∀ i : Fin 1, ∀ j : Fin 1,
        Int.natAbs ((0 + Int.ofNat i.1) - (4 + Int.ofNat j.1)) > 3 := by
    native_decide
  have hind :
      prob μ (cyl 0 b0 ∩ cyl 4 b0) = prob μ (cyl 0 b0) * prob μ (cyl 4 b0) := by
    simpa using
      (KDependent.prob_inter_cyl_eq_mul (μ := μ) (k := 3) (m := 1) (n := 1) (a := 0) (b := 4)
        hdep hsep b0 b0)
  -- stationarity: P(X4=0) = P(X0=0)
  have hs4 : prob μ (cyl 4 b0) = prob μ (cyl 0 b0) := by
    simpa using
      (Stationary.prob_cyl_add_nat (μ := μ) hstat (a := 0) (s := 4) (w := b0))

  -- translate the endpoint event to a disjoint union of length-5 cylinders.
  have hset : cyl 0 b0 ∩ cyl 4 b0 = cyl 0 w00100 ∪ cyl 0 w01010 := endpoints00_eq_union
  have hne : w00100 ≠ w01010 := by
    native_decide
  have hunion : prob μ (cyl 0 w00100 ∪ cyl 0 w01010) =
      prob μ (cyl 0 w00100) + prob μ (cyl 0 w01010) :=
    prob_union_cyl_of_ne (μ := μ) (a := 0) hne

  -- now substitute everything
  have hb0 : prob μ (cyl 0 b0) = 1 - prob μ (cyl 0 b1) := prob_b0 (μ := μ)
  calc
    prob μ (cyl 0 w00100) + prob μ (cyl 0 w01010) =
        prob μ (cyl 0 b0 ∩ cyl 4 b0) := by
          simpa [hset, hunion]
    _ = prob μ (cyl 0 b0) * prob μ (cyl 4 b0) := hind
    _ = prob μ (cyl 0 b0) * prob μ (cyl 0 b0) := by simp [hs4]
    _ = (1 - prob μ (cyl 0 b1)) ^ 2 := by
          -- rewrite `prob(b0)` as `1 - prob(b1)`
          simpa [hb0, pow_two, mul_comm, mul_left_comm, mul_assoc]

theorem prob_endpoints10 (μ : Measure State) [IsProbabilityMeasure μ]
    (hstat : Stationary μ) (hdep : KDependent 3 μ) :
    prob μ (cyl 0 w10010) + prob μ (cyl 0 w10100) =
      prob μ (cyl 0 b1) * (1 - prob μ (cyl 0 b1)) := by
  classical
  have hsep :
      ∀ i : Fin 1, ∀ j : Fin 1,
        Int.natAbs ((0 + Int.ofNat i.1) - (4 + Int.ofNat j.1)) > 3 := by
    native_decide
  have hind :
      prob μ (cyl 0 b1 ∩ cyl 4 b0) = prob μ (cyl 0 b1) * prob μ (cyl 4 b0) := by
    simpa using
      (KDependent.prob_inter_cyl_eq_mul (μ := μ) (k := 3) (m := 1) (n := 1) (a := 0) (b := 4)
        hdep hsep b1 b0)
  -- stationarity: P(X4=0) = P(X0=0)
  have hs4 : prob μ (cyl 4 b0) = prob μ (cyl 0 b0) := by
    simpa using
      (Stationary.prob_cyl_add_nat (μ := μ) hstat (a := 0) (s := 4) (w := b0))

  have hset : cyl 0 b1 ∩ cyl 4 b0 = cyl 0 w10010 ∪ cyl 0 w10100 := endpoints10_eq_union
  have hne : w10010 ≠ w10100 := by
    native_decide
  have hunion : prob μ (cyl 0 w10010 ∪ cyl 0 w10100) =
      prob μ (cyl 0 w10010) + prob μ (cyl 0 w10100) :=
    prob_union_cyl_of_ne (μ := μ) (a := 0) hne
  have hb0 : prob μ (cyl 0 b0) = 1 - prob μ (cyl 0 b1) := prob_b0 (μ := μ)

  calc
    prob μ (cyl 0 w10010) + prob μ (cyl 0 w10100) =
        prob μ (cyl 0 b1 ∩ cyl 4 b0) := by
          simpa [hset, hunion]
    _ = prob μ (cyl 0 b1) * prob μ (cyl 4 b0) := hind
    _ = prob μ (cyl 0 b1) * prob μ (cyl 0 b0) := by simp [hs4]
    _ = prob μ (cyl 0 b1) * (1 - prob μ (cyl 0 b1)) := by simp [hb0]

/-
## Finishing the k=3 contradiction (`PROOF_k_le_5.md`, Section 2)

We now derive:
1. explicit formulas for length-5 cylinder probabilities in terms of `p := P(X₀=1)`,
2. the quadratic constraint `3 p^2 - 6 p + 2 = 0`, and
3. the “(*)” identity
     (1-2p)(3p-1) = (1-p)(p^2-5p+2),
then invoke the kernel theorem `no_k3_kernel`.
-/

/-! ### Some basic set equalities -/

lemma cyl01_eq_cyl1_b1 : cyl 0 w01 = cyl 1 b1 := by
  ext ω
  constructor
  · intro h
    have h1 : ω.1 1 = true := by
      simpa [w01] using
        (bit_eq_of_mem_cyl (h := h) (i := (1 : Fin 2)))
    have hb : block 1 1 ω = b1 := by
      funext j
      fin_cases j
      simp [block, b1, h1]
    simpa [cyl] using hb
  · intro h
    have h1 : ω.1 1 = true := by
      simpa [b1, add_assoc, add_left_comm, add_comm] using
        (bit_eq_of_mem_cyl (h := h) (i := (0 : Fin 1)))
    have h0 : ω.1 0 = false := by
      simpa [add_assoc] using (true_prev_false ω (i := 0) (by simpa [add_assoc] using h1))
    have hw : block 0 2 ω = w01 := by
      funext j
      fin_cases j <;> simp [block, w01, h0, h1]
    simpa [cyl] using hw

lemma cyl_w100_eq : cyl 0 w100 = cyl 0 w10010 := by
  ext ω
  constructor
  · intro h
    have h0 : ω.1 0 = true := by
      simpa [w100] using
        (bit_eq_of_mem_cyl (h := h) (i := (0 : Fin 3)))
    have h1 : ω.1 1 = false := by
      simpa [w100] using
        (bit_eq_of_mem_cyl (h := h) (i := (1 : Fin 3)))
    have h2 : ω.1 2 = false := by
      simpa [w100] using
        (bit_eq_of_mem_cyl (h := h) (i := (2 : Fin 3)))
    have h3 : ω.1 3 = true := by
      simpa [add_assoc] using twoZeros_next_true ω (i := 1) h1 h2
    have h4 : ω.1 4 = false := by
      simpa [add_assoc] using true_next_false ω (i := 3) (by simpa [add_assoc] using h3)
    have hw : block 0 5 ω = w10010 := by
      funext j
      fin_cases j <;> simp [block, w10010, h0, h1, h2, h3, h4]
    simpa [cyl] using hw
  · intro h
    have h0 : ω.1 0 = true := by
      simpa [w10010] using
        (bit_eq_of_mem_cyl (h := h) (i := (0 : Fin 5)))
    have h1 : ω.1 1 = false := by
      simpa [w10010] using
        (bit_eq_of_mem_cyl (h := h) (i := (1 : Fin 5)))
    have h2 : ω.1 2 = false := by
      simpa [w10010] using
        (bit_eq_of_mem_cyl (h := h) (i := (2 : Fin 5)))
    have hu : block 0 3 ω = w100 := by
      funext j
      fin_cases j <;> simp [block, w100, h0, h1, h2]
    simpa [cyl] using hu

lemma cyl_w00_eq_union : cyl 0 w00 = cyl 0 w00100 ∪ cyl 0 w00101 := by
  ext ω
  constructor
  · intro h
    have h0 : ω.1 0 = false := by
      simpa [w00] using
        (bit_eq_of_mem_cyl (h := h) (i := (0 : Fin 2)))
    have h1 : ω.1 1 = false := by
      simpa [w00] using
        (bit_eq_of_mem_cyl (h := h) (i := (1 : Fin 2)))
    have h2 : ω.1 2 = true := by
      simpa [add_assoc] using twoZeros_next_true ω (i := 0) h0 h1
    have h3 : ω.1 3 = false := by
      simpa [add_assoc] using true_next_false ω (i := 2) (by simpa [add_assoc] using h2)
    cases h4 : ω.1 4
    · left
      have hw : block 0 5 ω = w00100 := by
        funext j
        fin_cases j <;> simp [block, w00100, h0, h1, h2, h3, h4]
      simpa [cyl] using hw
    · right
      have hw : block 0 5 ω = w00101 := by
        funext j
        fin_cases j <;> simp [block, w00101, h0, h1, h2, h3, h4]
      simpa [cyl] using hw
  · intro h
    rcases h with h | h
    · have h0 : ω.1 0 = false := by
        simpa [w00100] using
          (bit_eq_of_mem_cyl (h := h) (i := (0 : Fin 5)))
      have h1 : ω.1 1 = false := by
        simpa [w00100] using
          (bit_eq_of_mem_cyl (h := h) (i := (1 : Fin 5)))
      have hw : block 0 2 ω = w00 := by
        funext j
        fin_cases j <;> simp [block, w00, h0, h1]
      simpa [cyl] using hw
    · have h0 : ω.1 0 = false := by
        simpa [w00101] using
          (bit_eq_of_mem_cyl (h := h) (i := (0 : Fin 5)))
      have h1 : ω.1 1 = false := by
        simpa [w00101] using
          (bit_eq_of_mem_cyl (h := h) (i := (1 : Fin 5)))
      have hw : block 0 2 ω = w00 := by
        funext j
        fin_cases j <;> simp [block, w00, h0, h1]
      simpa [cyl] using hw

/-! ### Length-5 cylinder probabilities in terms of `p` -/

theorem prob_w10100_eq_prob_w00101 (μ : Measure State) [IsProbabilityMeasure μ] (hstat : Stationary μ) :
    prob μ (cyl 0 w10100) = prob μ (cyl 0 w00101) := by
  have h0101 := prob_eq_u0101 (μ := μ) hstat
  have h1010 := prob_eq_u1010 (μ := μ) hstat
  linarith

theorem prob_w10010_eq_one_sub_two_p (μ : Measure State) [IsProbabilityMeasure μ]
    (hstat : Stationary μ) (hdep : KDependent 3 μ) :
    prob μ (cyl 0 w10010) = 1 - 2 * prob μ (cyl 0 b1) := by
  set p : ℝ := prob μ (cyl 0 b1)
  have hg : prob μ (cyl 0 w10101) = p ^ 2 := by
    simpa [p] using prob_10101_eq_p2 (μ := μ) hstat hdep
  have h0010 := prob_eq_u0010 (μ := μ) hstat
  have h0101 := prob_eq_u0101 (μ := μ) hstat
  have hend00 : prob μ (cyl 0 w00100) + prob μ (cyl 0 w01010) = (1 - p) ^ 2 := by
    simpa [p] using prob_endpoints00 (μ := μ) hstat hdep
  have hend00' : prob μ (cyl 0 w10010) + prob μ (cyl 0 w10101) = (1 - p) ^ 2 := by
    linarith [hend00, h0101, h0010]
  have he : prob μ (cyl 0 w10010) = (1 - p) ^ 2 - p ^ 2 := by
    linarith [hend00', hg]
  have hsimp : (1 - p) ^ 2 - p ^ 2 = 1 - 2 * p := by ring
  simpa [p, hsimp] using he

theorem prob_w00101_eq_three_p_sub_one_sub_p_sq (μ : Measure State) [IsProbabilityMeasure μ]
    (hstat : Stationary μ) (hdep : KDependent 3 μ) :
    prob μ (cyl 0 w00101) =
      3 * prob μ (cyl 0 b1) - 1 - (prob μ (cyl 0 b1)) ^ 2 := by
  set p : ℝ := prob μ (cyl 0 b1)
  have hf : prob μ (cyl 0 w10100) = prob μ (cyl 0 w00101) :=
    prob_w10100_eq_prob_w00101 (μ := μ) hstat
  have hend10 : prob μ (cyl 0 w10010) + prob μ (cyl 0 w10100) = p * (1 - p) := by
    simpa [p] using prob_endpoints10 (μ := μ) hstat hdep
  have he : prob μ (cyl 0 w10010) = 1 - 2 * p := by
    simpa [p] using prob_w10010_eq_one_sub_two_p (μ := μ) hstat hdep
  have hend10' : prob μ (cyl 0 w10010) + prob μ (cyl 0 w00101) = p * (1 - p) := by
    simpa [hf] using hend10
  have hb : prob μ (cyl 0 w00101) = p * (1 - p) - prob μ (cyl 0 w10010) := by
    linarith [hend10']
  have hb' : prob μ (cyl 0 w00101) = p * (1 - p) - (1 - 2 * p) := by
    simpa [he] using hb
  have hsimp : p * (1 - p) - (1 - 2 * p) = 3 * p - 1 - p ^ 2 := by ring
  simpa [p, hsimp] using hb'

theorem prob_w00100_eq_p_sq_sub_five_p_add_two (μ : Measure State) [IsProbabilityMeasure μ]
    (hstat : Stationary μ) (hdep : KDependent 3 μ) :
    prob μ (cyl 0 w00100) =
      (prob μ (cyl 0 b1)) ^ 2 - 5 * prob μ (cyl 0 b1) + 2 := by
  set p : ℝ := prob μ (cyl 0 b1)
  have h0010 := prob_eq_u0010 (μ := μ) hstat
  have he : prob μ (cyl 0 w10010) = 1 - 2 * p := by
    simpa [p] using prob_w10010_eq_one_sub_two_p (μ := μ) hstat hdep
  have hb : prob μ (cyl 0 w00101) = 3 * p - 1 - p ^ 2 := by
    simpa [p] using prob_w00101_eq_three_p_sub_one_sub_p_sq (μ := μ) hstat hdep
  have ha : prob μ (cyl 0 w00100) = prob μ (cyl 0 w10010) - prob μ (cyl 0 w00101) := by
    linarith [h0010]
  have ha' : prob μ (cyl 0 w00100) = (1 - 2 * p) - (3 * p - 1 - p ^ 2) := by
    simpa [he, hb] using ha
  have hsimp : (1 - 2 * p) - (3 * p - 1 - p ^ 2) = p ^ 2 - 5 * p + 2 := by ring
  simpa [p, hsimp] using ha'

theorem prob_w01010_eq_three_p_sub_one (μ : Measure State) [IsProbabilityMeasure μ]
    (hstat : Stationary μ) (hdep : KDependent 3 μ) :
    prob μ (cyl 0 w01010) = 3 * prob μ (cyl 0 b1) - 1 := by
  set p : ℝ := prob μ (cyl 0 b1)
  have h0101 := prob_eq_u0101 (μ := μ) hstat
  have hb : prob μ (cyl 0 w00101) = 3 * p - 1 - p ^ 2 := by
    simpa [p] using prob_w00101_eq_three_p_sub_one_sub_p_sq (μ := μ) hstat hdep
  have hg : prob μ (cyl 0 w10101) = p ^ 2 := by
    simpa [p] using prob_10101_eq_p2 (μ := μ) hstat hdep
  have hd : prob μ (cyl 0 w01010) = prob μ (cyl 0 w00101) + prob μ (cyl 0 w10101) := by
    simpa using h0101
  have hd' : prob μ (cyl 0 w01010) = (3 * p - 1 - p ^ 2) + p ^ 2 := by
    simpa [hb, hg] using hd
  have hsimp : (3 * p - 1 - p ^ 2) + p ^ 2 = 3 * p - 1 := by ring
  simpa [p, hsimp] using hd'

theorem prob_w01001_eq_one_sub_two_p (μ : Measure State) [IsProbabilityMeasure μ]
    (hstat : Stationary μ) (hdep : KDependent 3 μ) :
    prob μ (cyl 0 w01001) = 1 - 2 * prob μ (cyl 0 b1) := by
  have h1001 := prob_eq_u1001 (μ := μ) hstat
  have he : prob μ (cyl 0 w10010) = 1 - 2 * prob μ (cyl 0 b1) :=
    prob_w10010_eq_one_sub_two_p (μ := μ) hstat hdep
  linarith

/-! ### A length-6 split forces the quadratic `3p^2 - 6p + 2 = 0` -/

lemma cyl_w100101_eq_cyl_succ_w00101 : cyl 0 w100101 = cyl 1 w00101 := by
  ext ω
  constructor
  · intro h
    have h1 : ω.1 1 = false := by
      simpa [w100101] using
        (bit_eq_of_mem_cyl (h := h) (i := (1 : Fin 6)))
    have h2 : ω.1 2 = false := by
      simpa [w100101] using
        (bit_eq_of_mem_cyl (h := h) (i := (2 : Fin 6)))
    have h3 : ω.1 3 = true := by
      simpa [w100101] using
        (bit_eq_of_mem_cyl (h := h) (i := (3 : Fin 6)))
    have h4 : ω.1 4 = false := by
      simpa [w100101] using
        (bit_eq_of_mem_cyl (h := h) (i := (4 : Fin 6)))
    have h5 : ω.1 5 = true := by
      simpa [w100101] using
        (bit_eq_of_mem_cyl (h := h) (i := (5 : Fin 6)))
    have hu : block 1 5 ω = w00101 := by
      funext j
      fin_cases j <;> simp [block, w00101, h1, h2, h3, h4, h5, add_assoc, add_left_comm, add_comm]
    simpa [cyl] using hu
  · intro h
    have h1 : ω.1 1 = false := by
      simpa [w00101, add_assoc, add_left_comm, add_comm] using
        (bit_eq_of_mem_cyl (h := h) (i := (0 : Fin 5)))
    have h2 : ω.1 2 = false := by
      simpa [w00101, add_assoc, add_left_comm, add_comm] using
        (bit_eq_of_mem_cyl (h := h) (i := (1 : Fin 5)))
    have h3 : ω.1 3 = true := by
      simpa [w00101, add_assoc, add_left_comm, add_comm] using
        (bit_eq_of_mem_cyl (h := h) (i := (2 : Fin 5)))
    have h4 : ω.1 4 = false := by
      simpa [w00101, add_assoc, add_left_comm, add_comm] using
        (bit_eq_of_mem_cyl (h := h) (i := (3 : Fin 5)))
    have h5 : ω.1 5 = true := by
      simpa [w00101, add_assoc, add_left_comm, add_comm] using
        (bit_eq_of_mem_cyl (h := h) (i := (4 : Fin 5)))
    have h0 : ω.1 0 = true := by
      simpa [add_assoc] using twoZeros_prev_true ω (i := 0) h1 h2
    have hw : block 0 6 ω = w100101 := by
      funext j
      fin_cases j <;> simp [block, w100101, h0, h1, h2, h3, h4, h5]
    simpa [cyl] using hw

lemma cyl_w101001_eq_cyl_w10100 : cyl 0 w101001 = cyl 0 w10100 := by
  ext ω
  constructor
  · intro h
    have h0 : ω.1 0 = true := by
      simpa [w101001] using
        (bit_eq_of_mem_cyl (h := h) (i := (0 : Fin 6)))
    have h1 : ω.1 1 = false := by
      simpa [w101001] using
        (bit_eq_of_mem_cyl (h := h) (i := (1 : Fin 6)))
    have h2 : ω.1 2 = true := by
      simpa [w101001] using
        (bit_eq_of_mem_cyl (h := h) (i := (2 : Fin 6)))
    have h3 : ω.1 3 = false := by
      simpa [w101001] using
        (bit_eq_of_mem_cyl (h := h) (i := (3 : Fin 6)))
    have h4 : ω.1 4 = false := by
      simpa [w101001] using
        (bit_eq_of_mem_cyl (h := h) (i := (4 : Fin 6)))
    have hu : block 0 5 ω = w10100 := by
      funext j
      fin_cases j <;> simp [block, w10100, h0, h1, h2, h3, h4]
    simpa [cyl] using hu
  · intro h
    have h0 : ω.1 0 = true := by
      simpa [w10100] using
        (bit_eq_of_mem_cyl (h := h) (i := (0 : Fin 5)))
    have h1 : ω.1 1 = false := by
      simpa [w10100] using
        (bit_eq_of_mem_cyl (h := h) (i := (1 : Fin 5)))
    have h2 : ω.1 2 = true := by
      simpa [w10100] using
        (bit_eq_of_mem_cyl (h := h) (i := (2 : Fin 5)))
    have h3 : ω.1 3 = false := by
      simpa [w10100] using
        (bit_eq_of_mem_cyl (h := h) (i := (3 : Fin 5)))
    have h4 : ω.1 4 = false := by
      simpa [w10100] using
        (bit_eq_of_mem_cyl (h := h) (i := (4 : Fin 5)))
    have h5 : ω.1 5 = true := by
      simpa [add_assoc] using twoZeros_next_true ω (i := 3) h3 h4
    have hw : block 0 6 ω = w101001 := by
      funext j
      fin_cases j <;> simp [block, w101001, h0, h1, h2, h3, h4, h5]
    simpa [cyl] using hw

lemma endpoints1_last01_eq_union :
    cyl 0 b1 ∩ cyl 4 w01 = cyl 0 w100101 ∪ cyl 0 w101001 := by
  ext ω
  constructor
  · rintro ⟨h0, h45⟩
    have h0' : ω.1 0 = true := by
      simpa [b1] using
        (bit_eq_of_mem_cyl (h := h0) (i := (0 : Fin 1)))
    have h4 : ω.1 4 = false := by
      simpa [w01, add_assoc, add_left_comm, add_comm] using
        (bit_eq_of_mem_cyl (h := h45) (i := (0 : Fin 2)))
    have h5 : ω.1 5 = true := by
      simpa [w01, add_assoc, add_left_comm, add_comm] using
        (bit_eq_of_mem_cyl (h := h45) (i := (1 : Fin 2)))
    have h1 : ω.1 1 = false := by
      simpa [add_assoc] using true_next_false ω (i := 0) (by simpa [add_assoc] using h0')
    cases h2 : ω.1 2
    · left
      have h3 : ω.1 3 = true := by
        simpa [add_assoc] using twoZeros_next_true ω (i := 1) h1 h2
      have hw : block 0 6 ω = w100101 := by
        funext j
        fin_cases j <;> simp [block, w100101, h0', h1, h2, h3, h4, h5]
      simpa [cyl] using hw
    · right
      have h3 : ω.1 3 = false := by
        simpa [add_assoc] using true_next_false ω (i := 2) (by simpa [add_assoc] using h2)
      have hw : block 0 6 ω = w101001 := by
        funext j
        fin_cases j <;> simp [block, w101001, h0', h1, h2, h3, h4, h5]
      simpa [cyl] using hw
  · intro h
    constructor
    · rcases h with h | h
      · have h0' : ω.1 0 = true := by
          simpa [w100101] using
            (bit_eq_of_mem_cyl (h := h) (i := (0 : Fin 6)))
        have hb : block 0 1 ω = b1 := by
          funext j; fin_cases j; simp [block, b1, h0']
        simpa [cyl] using hb
      · have h0' : ω.1 0 = true := by
          simpa [w101001] using
            (bit_eq_of_mem_cyl (h := h) (i := (0 : Fin 6)))
        have hb : block 0 1 ω = b1 := by
          funext j; fin_cases j; simp [block, b1, h0']
        simpa [cyl] using hb
    · rcases h with h | h
      · have h4 : ω.1 4 = false := by
          simpa [w100101] using
            (bit_eq_of_mem_cyl (h := h) (i := (4 : Fin 6)))
        have h5 : ω.1 5 = true := by
          simpa [w100101] using
            (bit_eq_of_mem_cyl (h := h) (i := (5 : Fin 6)))
        have hb : block 4 2 ω = w01 := by
          funext j; fin_cases j <;> simp [block, w01, h4, h5, add_assoc, add_left_comm, add_comm]
        simpa [cyl] using hb
      · have h4 : ω.1 4 = false := by
          simpa [w101001] using
            (bit_eq_of_mem_cyl (h := h) (i := (4 : Fin 6)))
        have h5 : ω.1 5 = true := by
          simpa [w101001] using
            (bit_eq_of_mem_cyl (h := h) (i := (5 : Fin 6)))
        have hb : block 4 2 ω = w01 := by
          funext j; fin_cases j <;> simp [block, w01, h4, h5, add_assoc, add_left_comm, add_comm]
        simpa [cyl] using hb

theorem quadratic_of_len6 (μ : Measure State) [IsProbabilityMeasure μ]
    (hstat : Stationary μ) (hdep : KDependent 3 μ) :
    3 * (prob μ (cyl 0 b1)) ^ 2 - 6 * prob μ (cyl 0 b1) + 2 = 0 := by
  classical
  set p : ℝ := prob μ (cyl 0 b1)
  have hb : prob μ (cyl 0 w00101) = 3 * p - 1 - p ^ 2 := by
    simpa [p] using prob_w00101_eq_three_p_sub_one_sub_p_sq (μ := μ) hstat hdep
  -- Independence: X0 ⟂ (X4,X5) gives P(X0=1, X4X5=01) = p * p = p^2.
  have hsep :
      ∀ i : Fin 1, ∀ j : Fin 2,
        Int.natAbs ((0 + Int.ofNat i.1) - (4 + Int.ofNat j.1)) > 3 := by
    native_decide
  have hind :
      prob μ (cyl 0 b1 ∩ cyl 4 w01) = prob μ (cyl 0 b1) * prob μ (cyl 4 w01) := by
    simpa using
      (KDependent.prob_inter_cyl_eq_mul (μ := μ) (k := 3) (m := 1) (n := 2) (a := 0) (b := 4)
        hdep hsep b1 w01)
  -- Stationarity: shift the `01` cylinder from 4 back to 0.
  have hs4 : prob μ (cyl 4 w01) = prob μ (cyl 0 w01) := by
    simpa using
      (Stationary.prob_cyl_add_nat (μ := μ) hstat (a := 0) (s := 4) (w := w01))
  have h01 : prob μ (cyl 0 w01) = p := by
    have : prob μ (cyl 0 w01) = prob μ (cyl 1 b1) := by
      simpa [cyl01_eq_cyl1_b1] using (rfl : prob μ (cyl 0 w01) = prob μ (cyl 0 w01))
    -- stationarity makes `P(X₁=1) = P(X₀=1) = p`.
    have hs : prob μ (cyl 1 b1) = prob μ (cyl 0 b1) :=
      Stationary.prob_cyl_succ (μ := μ) hstat (a := 0) (w := b1)
    simpa [p] using (this.trans hs)

  have hrhs : prob μ (cyl 0 b1) * prob μ (cyl 4 w01) = p ^ 2 := by
    have hb1 : prob μ (cyl 0 b1) = p := by simpa [p]
    calc
      prob μ (cyl 0 b1) * prob μ (cyl 4 w01) =
          p * prob μ (cyl 4 w01) := by simpa [hb1]
      _ = p * prob μ (cyl 0 w01) := by simp [hs4]
      _ = p * p := by simp [h01]
      _ = p ^ 2 := by simp [pow_two]

  -- Express the LHS as a disjoint union of the two compatible length-6 cylinders.
  have hset : cyl 0 b1 ∩ cyl 4 w01 = cyl 0 w100101 ∪ cyl 0 w101001 := endpoints1_last01_eq_union
  have hne : w100101 ≠ w101001 := by
    native_decide
  have hunion : prob μ (cyl 0 w100101 ∪ cyl 0 w101001) =
      prob μ (cyl 0 w100101) + prob μ (cyl 0 w101001) :=
    prob_union_cyl_of_ne (μ := μ) (a := 0) hne
  have h100101 : prob μ (cyl 0 w100101) = prob μ (cyl 0 w00101) := by
    have hs : prob μ (cyl 1 w00101) = prob μ (cyl 0 w00101) :=
      Stationary.prob_cyl_succ (μ := μ) hstat (a := 0) (w := w00101)
    -- `100101` is the unique left-extension of `00101`.
    have hset' : cyl 0 w100101 = cyl 1 w00101 := cyl_w100101_eq_cyl_succ_w00101
    simpa [hset', hs] using (rfl : prob μ (cyl 0 w100101) = prob μ (cyl 0 w100101))
  have h101001 : prob μ (cyl 0 w101001) = prob μ (cyl 0 w10100) := by
    have hset' : cyl 0 w101001 = cyl 0 w10100 := cyl_w101001_eq_cyl_w10100
    simpa [hset'] using (rfl : prob μ (cyl 0 w101001) = prob μ (cyl 0 w101001))
  have hf : prob μ (cyl 0 w10100) = prob μ (cyl 0 w00101) :=
    prob_w10100_eq_prob_w00101 (μ := μ) hstat

  have hlhs : prob μ (cyl 0 b1 ∩ cyl 4 w01) = 2 * prob μ (cyl 0 w00101) := by
    calc
      prob μ (cyl 0 b1 ∩ cyl 4 w01) = prob μ (cyl 0 w100101 ∪ cyl 0 w101001) := by
        simpa [hset]
      _ = prob μ (cyl 0 w100101) + prob μ (cyl 0 w101001) := hunion
      _ = prob μ (cyl 0 w00101) + prob μ (cyl 0 w10100) := by simp [h100101, h101001]
      _ = prob μ (cyl 0 w00101) + prob μ (cyl 0 w00101) := by simp [hf]
      _ = 2 * prob μ (cyl 0 w00101) := by ring

  have hfactor : prob μ (cyl 0 b1 ∩ cyl 4 w01) = p ^ 2 := by
    calc
      prob μ (cyl 0 b1 ∩ cyl 4 w01) = prob μ (cyl 0 b1) * prob μ (cyl 4 w01) := hind
      _ = p ^ 2 := hrhs

  have hb2 : 2 * prob μ (cyl 0 w00101) = p ^ 2 := by
    simpa [hlhs] using hfactor

  -- Substitute the length-5 formula for `P(00101)` and simplify.
  have hb2' : 2 * (3 * p - 1 - p ^ 2) = p ^ 2 := by
    simpa [hb] using hb2
  -- Rearrange.
  -- 2*(3p-1-p^2)=p^2 ↔ 3p^2 - 6p + 2 = 0
  nlinarith [hb2']

/-! ### The “(*)” identity at length 9 -/

lemma cyl_w10010100_eq_inter : cyl 0 w10010100 = cyl 0 w100 ∩ cyl 6 w00 := by
  ext ω
  constructor
  · intro h
    constructor
    · -- prefix `100`
      have h0 : ω.1 0 = true := by
        have := (bit_eq_of_mem_cyl (h := h) (i := (0 : Fin 8)))
        simpa [w10010100] using this
      have h1 : ω.1 1 = false := by
        have := (bit_eq_of_mem_cyl (h := h) (i := (1 : Fin 8)))
        simpa [w10010100] using this
      have h2 : ω.1 2 = false := by
        have := (bit_eq_of_mem_cyl (h := h) (i := (2 : Fin 8)))
        simpa [w10010100] using this
      have hu : block 0 3 ω = w100 := by
        funext j
        fin_cases j <;> simp [block, w100, h0, h1, h2]
      simpa [cyl] using hu
    · -- suffix `00` at 6..7
      have h6 : ω.1 6 = false := by
        have := (bit_eq_of_mem_cyl (h := h) (i := (6 : Fin 8)))
        simpa [w10010100] using this
      have h7 : ω.1 7 = false := by
        have := (bit_eq_of_mem_cyl (h := h) (i := (7 : Fin 8)))
        simpa [w10010100] using this
      have hu : block 6 2 ω = w00 := by
        funext j
        fin_cases j <;> simp [block, w00, h6, h7, add_assoc, add_left_comm, add_comm]
      simpa [cyl] using hu
  · rintro ⟨h100, h00⟩
    have h0 : ω.1 0 = true := by
      have := (bit_eq_of_mem_cyl (h := h100) (i := (0 : Fin 3)))
      simpa [w100] using this
    have h1 : ω.1 1 = false := by
      have := (bit_eq_of_mem_cyl (h := h100) (i := (1 : Fin 3)))
      simpa [w100] using this
    have h2 : ω.1 2 = false := by
      have := (bit_eq_of_mem_cyl (h := h100) (i := (2 : Fin 3)))
      simpa [w100] using this
    have h6 : ω.1 6 = false := by
      have := (bit_eq_of_mem_cyl (h := h00) (i := (0 : Fin 2)))
      simpa [w00, add_assoc, add_left_comm, add_comm] using this
    have h7 : ω.1 7 = false := by
      have := (bit_eq_of_mem_cyl (h := h00) (i := (1 : Fin 2)))
      simpa [w00, add_assoc, add_left_comm, add_comm] using this
    have h3 : ω.1 3 = true := by
      simpa [add_assoc] using twoZeros_next_true ω (i := 1) h1 h2
    have h4 : ω.1 4 = false := by
      simpa [add_assoc] using true_next_false ω (i := 3) (by simpa [add_assoc] using h3)
    have h5 : ω.1 5 = true := by
      simpa [add_assoc] using twoZeros_prev_true ω (i := 5) h6 h7
    have hw : block 0 8 ω = w10010100 := by
      funext j
      fin_cases j <;> simp [block, w10010100, h0, h1, h2, h3, h4, h5, h6, h7]
    simpa [cyl] using hw

lemma cyl_b1_u0100_eq_union :
    cyl 0 b1 ∩ cyl 4 u0100 = cyl 0 w10010100 ∪ cyl 0 w10100100 := by
  ext ω
  constructor
  · rintro ⟨h0, h4⟩
    have h0' : ω.1 0 = true := by
      have := (bit_eq_of_mem_cyl (h := h0) (i := (0 : Fin 1)))
      simpa [b1] using this
    have h4' : ω.1 4 = false := by
      have := (bit_eq_of_mem_cyl (h := h4) (i := (0 : Fin 4)))
      simpa [u0100, add_assoc, add_left_comm, add_comm] using this
    have h5 : ω.1 5 = true := by
      have := (bit_eq_of_mem_cyl (h := h4) (i := (1 : Fin 4)))
      simpa [u0100, add_assoc, add_left_comm, add_comm] using this
    have h6 : ω.1 6 = false := by
      have := (bit_eq_of_mem_cyl (h := h4) (i := (2 : Fin 4)))
      simpa [u0100, add_assoc, add_left_comm, add_comm] using this
    have h7 : ω.1 7 = false := by
      have := (bit_eq_of_mem_cyl (h := h4) (i := (3 : Fin 4)))
      simpa [u0100, add_assoc, add_left_comm, add_comm] using this
    have h1 : ω.1 1 = false := by
      simpa [add_assoc] using true_next_false ω (i := 0) (by simpa [add_assoc] using h0')
    cases h2 : ω.1 2
    · left
      have h3 : ω.1 3 = true := by
        simpa [add_assoc] using twoZeros_next_true ω (i := 1) h1 h2
      have hw : block 0 8 ω = w10010100 := by
        funext j
        fin_cases j <;> simp [block, w10010100, h0', h1, h2, h3, h4', h5, h6, h7]
      simpa [cyl] using hw
    · right
      have h3 : ω.1 3 = false := by
        simpa [add_assoc] using true_next_false ω (i := 2) (by simpa [add_assoc] using h2)
      have hw : block 0 8 ω = w10100100 := by
        funext j
        fin_cases j <;> simp [block, w10100100, h0', h1, h2, h3, h4', h5, h6, h7]
      simpa [cyl] using hw
  · intro h
    constructor
    · rcases h with h | h
      · have h0' : ω.1 0 = true := by
          have := (bit_eq_of_mem_cyl (h := h) (i := (0 : Fin 8)))
          simpa [w10010100] using this
        have hb : block 0 1 ω = b1 := by
          funext j; fin_cases j; simp [block, b1, h0']
        simpa [cyl] using hb
      · have h0' : ω.1 0 = true := by
          have := (bit_eq_of_mem_cyl (h := h) (i := (0 : Fin 8)))
          simpa [w10100100] using this
        have hb : block 0 1 ω = b1 := by
          funext j; fin_cases j; simp [block, b1, h0']
        simpa [cyl] using hb
    · rcases h with h | h
      · have h4' : ω.1 4 = false := by
          have := (bit_eq_of_mem_cyl (h := h) (i := (4 : Fin 8)))
          simpa [w10010100] using this
        have h5 : ω.1 5 = true := by
          have := (bit_eq_of_mem_cyl (h := h) (i := (5 : Fin 8)))
          simpa [w10010100] using this
        have h6 : ω.1 6 = false := by
          have := (bit_eq_of_mem_cyl (h := h) (i := (6 : Fin 8)))
          simpa [w10010100] using this
        have h7 : ω.1 7 = false := by
          have := (bit_eq_of_mem_cyl (h := h) (i := (7 : Fin 8)))
          simpa [w10010100] using this
        have hb : block 4 4 ω = u0100 := by
          funext j
          fin_cases j <;> simp [block, u0100, h4', h5, h6, h7, add_assoc, add_left_comm, add_comm]
        simpa [cyl] using hb
      · have h4' : ω.1 4 = false := by
          have := (bit_eq_of_mem_cyl (h := h) (i := (4 : Fin 8)))
          simpa [w10100100] using this
        have h5 : ω.1 5 = true := by
          have := (bit_eq_of_mem_cyl (h := h) (i := (5 : Fin 8)))
          simpa [w10100100] using this
        have h6 : ω.1 6 = false := by
          have := (bit_eq_of_mem_cyl (h := h) (i := (6 : Fin 8)))
          simpa [w10100100] using this
        have h7 : ω.1 7 = false := by
          have := (bit_eq_of_mem_cyl (h := h) (i := (7 : Fin 8)))
          simpa [w10100100] using this
        have hb : block 4 4 ω = u0100 := by
          funext j
          fin_cases j <;> simp [block, u0100, h4', h5, h6, h7, add_assoc, add_left_comm, add_comm]
        simpa [cyl] using hb

lemma cyl_w110100100_empty : cyl 0 w110100100 = (∅ : Set State) := by
  ext ω
  constructor
  · intro h
    have h0 : ω.1 0 = true := by
      have := (bit_eq_of_mem_cyl (h := h) (i := (0 : Fin 9)))
      simpa [w110100100] using this
    have h1 : ω.1 1 = true := by
      have := (bit_eq_of_mem_cyl (h := h) (i := (1 : Fin 9)))
      simpa [w110100100] using this
    rcases ω.2 with ⟨h11, -⟩
    exact (h11 0) ⟨h0, by simpa [add_assoc] using h1⟩
  · intro h
    exact False.elim (by simpa using h)

lemma prob_w10100100_eq_prob_w010100100 (μ : Measure State) [IsProbabilityMeasure μ]
    (hstat : Stationary μ) :
    prob μ (cyl 0 w10100100) = prob μ (cyl 0 w010100100) := by
  classical
  -- Partition by the value of `X_{-1}`.
  have hset : cyl 0 w10100100 = cyl (-1) w010100100 ∪ cyl (-1) w110100100 := by
    ext ω
    constructor
    · intro h
      cases hneg : ω.1 (-1)
      · left
        have hb : block (-1) 9 ω = w010100100 := by
          -- `w010100100` is `0` followed by `w10100100`.
          have h0 : ω.1 0 = true := by
            have := (bit_eq_of_mem_cyl (h := h) (i := (0 : Fin 8)))
            simpa [w10100100] using this
          have h1 : ω.1 1 = false := by
            have := (bit_eq_of_mem_cyl (h := h) (i := (1 : Fin 8)))
            simpa [w10100100] using this
          have h2 : ω.1 2 = true := by
            have := (bit_eq_of_mem_cyl (h := h) (i := (2 : Fin 8)))
            simpa [w10100100] using this
          have h3 : ω.1 3 = false := by
            have := (bit_eq_of_mem_cyl (h := h) (i := (3 : Fin 8)))
            simpa [w10100100] using this
          have h4 : ω.1 4 = false := by
            have := (bit_eq_of_mem_cyl (h := h) (i := (4 : Fin 8)))
            simpa [w10100100] using this
          have h5 : ω.1 5 = true := by
            have := (bit_eq_of_mem_cyl (h := h) (i := (5 : Fin 8)))
            simpa [w10100100] using this
          have h6 : ω.1 6 = false := by
            have := (bit_eq_of_mem_cyl (h := h) (i := (6 : Fin 8)))
            simpa [w10100100] using this
          have h7 : ω.1 7 = false := by
            have := (bit_eq_of_mem_cyl (h := h) (i := (7 : Fin 8)))
            simpa [w10100100] using this
          funext j
          fin_cases j <;> simp [block, w010100100, hneg, h0, h1, h2, h3, h4, h5, h6, h7, add_assoc]
        simpa [cyl] using hb
      · right
        have hb : block (-1) 9 ω = w110100100 := by
          -- `w110100100` is `1` followed by `w10100100`.
          have h0 : ω.1 0 = true := by
            have := (bit_eq_of_mem_cyl (h := h) (i := (0 : Fin 8)))
            simpa [w10100100] using this
          have h1 : ω.1 1 = false := by
            have := (bit_eq_of_mem_cyl (h := h) (i := (1 : Fin 8)))
            simpa [w10100100] using this
          have h2 : ω.1 2 = true := by
            have := (bit_eq_of_mem_cyl (h := h) (i := (2 : Fin 8)))
            simpa [w10100100] using this
          have h3 : ω.1 3 = false := by
            have := (bit_eq_of_mem_cyl (h := h) (i := (3 : Fin 8)))
            simpa [w10100100] using this
          have h4 : ω.1 4 = false := by
            have := (bit_eq_of_mem_cyl (h := h) (i := (4 : Fin 8)))
            simpa [w10100100] using this
          have h5 : ω.1 5 = true := by
            have := (bit_eq_of_mem_cyl (h := h) (i := (5 : Fin 8)))
            simpa [w10100100] using this
          have h6 : ω.1 6 = false := by
            have := (bit_eq_of_mem_cyl (h := h) (i := (6 : Fin 8)))
            simpa [w10100100] using this
          have h7 : ω.1 7 = false := by
            have := (bit_eq_of_mem_cyl (h := h) (i := (7 : Fin 8)))
            simpa [w10100100] using this
          funext j
          fin_cases j <;> simp [block, w110100100, hneg, h0, h1, h2, h3, h4, h5, h6, h7, add_assoc]
        simpa [cyl] using hb
    · intro h
      rcases h with h | h
      · -- drop the first bit
        have hb : block 0 8 ω = w10100100 := by
          funext j
          have := bit_eq_of_mem_cyl (h := h) (i := ⟨j.1.succ, Nat.succ_lt_succ j.2⟩)
          simpa [cyl, block, w010100100, w10100100, add_assoc, add_left_comm, add_comm] using this
        simpa [cyl] using hb
      · have hb : block 0 8 ω = w10100100 := by
          funext j
          have := bit_eq_of_mem_cyl (h := h) (i := ⟨j.1.succ, Nat.succ_lt_succ j.2⟩)
          simpa [cyl, block, w110100100, w10100100, add_assoc, add_left_comm, add_comm] using this
        simpa [cyl] using hb
  have hne : w010100100 ≠ w110100100 := by
    native_decide
  have hunion :
      prob μ (cyl (-1) w010100100 ∪ cyl (-1) w110100100) =
        prob μ (cyl (-1) w010100100) + prob μ (cyl (-1) w110100100) :=
    prob_union_cyl_of_ne (μ := μ) (a := -1) hne
  have hs0 : prob μ (cyl 0 w010100100) = prob μ (cyl (-1) w010100100) := by
    simpa using (Stationary.prob_cyl_succ (μ := μ) hstat (a := -1) (w := w010100100))
  have hs1 : prob μ (cyl 0 w110100100) = prob μ (cyl (-1) w110100100) := by
    simpa using (Stationary.prob_cyl_succ (μ := μ) hstat (a := -1) (w := w110100100))
  have hempty : prob μ (cyl 0 w110100100) = 0 := by
    simpa [prob_empty, cyl_w110100100_empty] using (rfl : prob μ (cyl 0 w110100100) = prob μ (cyl 0 w110100100))
  calc
    prob μ (cyl 0 w10100100) = prob μ (cyl (-1) w010100100 ∪ cyl (-1) w110100100) := by
      simpa [hset]
    _ = prob μ (cyl (-1) w010100100) + prob μ (cyl (-1) w110100100) := hunion
    _ = prob μ (cyl 0 w010100100) + prob μ (cyl 0 w110100100) := by simp [hs0, hs1]
    _ = prob μ (cyl 0 w010100100) := by simp [hempty]

lemma cyl_w010100100_eq_inter :
    cyl 0 w010100100 = cyl 0 b0 ∩ cyl 4 w00100 := by
  ext ω
  constructor
  · intro h
    constructor
    · have h0 : ω.1 0 = false := by
        have := (bit_eq_of_mem_cyl (h := h) (i := (0 : Fin 9)))
        simpa [w010100100] using this
      have hb : block 0 1 ω = b0 := by
        funext j; fin_cases j; simp [block, b0, h0]
      simpa [cyl] using hb
    · have hb : block 4 5 ω = w00100 := by
        funext j
        have := bit_eq_of_mem_cyl (h := h) (i := ⟨(j.1 + 4), by omega⟩)
        -- simplify the index arithmetic
        simpa [block, w010100100, w00100, add_assoc, add_left_comm, add_comm] using this
      simpa [cyl] using hb
  · rintro ⟨h0, h48⟩
    have h0' : ω.1 0 = false := by
      have := (bit_eq_of_mem_cyl (h := h0) (i := (0 : Fin 1)))
      simpa [b0] using this
    have h4 : ω.1 4 = false := by
      have := (bit_eq_of_mem_cyl (h := h48) (i := (0 : Fin 5)))
      simpa [w00100, add_assoc, add_left_comm, add_comm] using this
    have h5 : ω.1 5 = false := by
      have := (bit_eq_of_mem_cyl (h := h48) (i := (1 : Fin 5)))
      simpa [w00100, add_assoc, add_left_comm, add_comm] using this
    have h6 : ω.1 6 = true := by
      have := (bit_eq_of_mem_cyl (h := h48) (i := (2 : Fin 5)))
      simpa [w00100, add_assoc, add_left_comm, add_comm] using this
    have h7 : ω.1 7 = false := by
      have := (bit_eq_of_mem_cyl (h := h48) (i := (3 : Fin 5)))
      simpa [w00100, add_assoc, add_left_comm, add_comm] using this
    have h8 : ω.1 8 = false := by
      have := (bit_eq_of_mem_cyl (h := h48) (i := (4 : Fin 5)))
      simpa [w00100, add_assoc, add_left_comm, add_comm] using this
    have h3 : ω.1 3 = true := by
      simpa [add_assoc] using twoZeros_prev_true ω (i := 3) h4 h5
    have h2 : ω.1 2 = false := by
      simpa [add_assoc] using true_prev_false ω (i := 2) (by simpa [add_assoc] using h3)
    have h1 : ω.1 1 = true := by
      -- Otherwise we would have `000` at (0,1,2).
      rcases ω.2 with ⟨-, h000⟩
      have hnot : ¬(ω.1 0 = false ∧ ω.1 1 = false ∧ ω.1 2 = false) := by
        simpa [add_assoc] using h000 0
      cases h1 : ω.1 1
      · exfalso
        apply hnot
        exact ⟨h0', h1, h2⟩
      · simpa using h1
    have hw : block 0 9 ω = w010100100 := by
      funext j
      fin_cases j <;> simp [block, w010100100, h0', h1, h2, h3, h4, h5, h6, h7, h8]
    simpa [cyl] using hw

theorem star_identity (μ : Measure State) [IsProbabilityMeasure μ]
    (hstat : Stationary μ) (hdep : KDependent 3 μ) :
    (1 - 2 * prob μ (cyl 0 b1)) * (3 * prob μ (cyl 0 b1) - 1) =
      (1 - prob μ (cyl 0 b1)) *
        ((prob μ (cyl 0 b1)) ^ 2 - 5 * prob μ (cyl 0 b1) + 2) := by
  classical
  set p : ℝ := prob μ (cyl 0 b1)
  have he : prob μ (cyl 0 w10010) = 1 - 2 * p := by
    simpa [p] using prob_w10010_eq_one_sub_two_p (μ := μ) hstat hdep
  have ha : prob μ (cyl 0 w00100) = p ^ 2 - 5 * p + 2 := by
    simpa [p] using prob_w00100_eq_p_sq_sub_five_p_add_two (μ := μ) hstat hdep
  have hd : prob μ (cyl 0 w01010) = 3 * p - 1 := by
    simpa [p] using prob_w01010_eq_three_p_sub_one (μ := μ) hstat hdep

  -- Step A: compute `P(10100100) = (1-2p)(3p-1)`.
  have hsepA :
      ∀ i : Fin 3, ∀ j : Fin 2,
        Int.natAbs ((0 + Int.ofNat i.1) - (6 + Int.ofNat j.1)) > 3 := by
    native_decide
  have hindA :
      prob μ (cyl 0 w100 ∩ cyl 6 w00) = prob μ (cyl 0 w100) * prob μ (cyl 6 w00) := by
    simpa using
      (KDependent.prob_inter_cyl_eq_mul (μ := μ) (k := 3) (m := 3) (n := 2) (a := 0) (b := 6)
        hdep hsepA w100 w00)
  have hs00 : prob μ (cyl 6 w00) = prob μ (cyl 0 w00) := by
    simpa using
      (Stationary.prob_cyl_add_nat (μ := μ) hstat (a := 0) (s := 6) (w := w00))
  have h100 : prob μ (cyl 0 w100) = prob μ (cyl 0 w10010) := by
    simpa [cyl_w100_eq] using (rfl : prob μ (cyl 0 w100) = prob μ (cyl 0 w100))
  have h00 : prob μ (cyl 0 w00) = prob μ (cyl 0 w00100) + prob μ (cyl 0 w00101) := by
    have hne : w00100 ≠ w00101 := by
      native_decide
    have hunion :
        prob μ (cyl 0 w00100 ∪ cyl 0 w00101) =
          prob μ (cyl 0 w00100) + prob μ (cyl 0 w00101) :=
      prob_union_cyl_of_ne (μ := μ) (a := 0) hne
    have hset : cyl 0 w00 = cyl 0 w00100 ∪ cyl 0 w00101 := cyl_w00_eq_union
    simpa [hset] using hunion

  have hP10010100 : prob μ (cyl 0 w10010100) = (1 - 2 * p) ^ 2 := by
    have hset : cyl 0 w10010100 = cyl 0 w100 ∩ cyl 6 w00 := cyl_w10010100_eq_inter
    have hP : prob μ (cyl 0 w10010100) =
        prob μ (cyl 0 w100) * prob μ (cyl 6 w00) := by
      simpa [hset] using hindA
    -- Rewrite the factors using length-5 probabilities.
    have hP' : prob μ (cyl 0 w10010100) =
        prob μ (cyl 0 w10010) * prob μ (cyl 0 w10010) := by
      -- `P(100) = P(10010)` and `P(00) = P(10010)` (from `a+b=e`).
      have h0010 := prob_eq_u0010 (μ := μ) hstat
      -- `P(00) = P(00100)+P(00101) = P(10010)`
      have h00' : prob μ (cyl 0 w00) = prob μ (cyl 0 w10010) := by
        simpa [h00, h0010]
      simpa [h100, hs00, h00'] using hP
    have : prob μ (cyl 0 w10010100) = (1 - 2 * p) * (1 - 2 * p) := by
      simpa [he] using hP'
    simpa [pow_two] using this

  have hsepB :
      ∀ i : Fin 1, ∀ j : Fin 4,
        Int.natAbs ((0 + Int.ofNat i.1) - (4 + Int.ofNat j.1)) > 3 := by
    native_decide
  have hindB :
      prob μ (cyl 0 b1 ∩ cyl 4 u0100) = prob μ (cyl 0 b1) * prob μ (cyl 4 u0100) := by
    simpa using
      (KDependent.prob_inter_cyl_eq_mul (μ := μ) (k := 3) (m := 1) (n := 4) (a := 0) (b := 4)
        hdep hsepB b1 u0100)
  have hs_u0100 : prob μ (cyl 4 u0100) = prob μ (cyl 0 u0100) := by
    simpa using
      (Stationary.prob_cyl_add_nat (μ := μ) hstat (a := 0) (s := 4) (w := u0100))
  have hP_u0100 : prob μ (cyl 0 u0100) = prob μ (cyl 0 w01001) := by
    simpa [cyl_u0100_eq] using (rfl : prob μ (cyl 0 u0100) = prob μ (cyl 0 u0100))
  have hP01 : prob μ (cyl 0 u0100) = 1 - 2 * p := by
    have hc : prob μ (cyl 0 w01001) = 1 - 2 * p := by
      simpa [p] using prob_w01001_eq_one_sub_two_p (μ := μ) hstat hdep
    simpa [hP_u0100, hc]
  have hPsum : prob μ (cyl 0 w10010100) + prob μ (cyl 0 w10100100) = p * (1 - 2 * p) := by
    have hset : cyl 0 b1 ∩ cyl 4 u0100 = cyl 0 w10010100 ∪ cyl 0 w10100100 := cyl_b1_u0100_eq_union
    have hne : w10010100 ≠ w10100100 := by
      native_decide
    have hunion :
        prob μ (cyl 0 w10010100 ∪ cyl 0 w10100100) =
          prob μ (cyl 0 w10010100) + prob μ (cyl 0 w10100100) :=
      prob_union_cyl_of_ne (μ := μ) (a := 0) hne
    have : prob μ (cyl 0 w10010100 ∪ cyl 0 w10100100) = p * (1 - 2 * p) := by
      calc
        prob μ (cyl 0 w10010100 ∪ cyl 0 w10100100) = prob μ (cyl 0 b1 ∩ cyl 4 u0100) := by
          simpa [hset]
        _ = prob μ (cyl 0 b1) * prob μ (cyl 4 u0100) := hindB
        _ = p * (1 - 2 * p) := by simp [p, hs_u0100, hP01]
    simpa [hunion] using this
  have hP10100100 : prob μ (cyl 0 w10100100) = (1 - 2 * p) * (3 * p - 1) := by
    have : prob μ (cyl 0 w10100100) = p * (1 - 2 * p) - (1 - 2 * p) ^ 2 := by
      linarith [hPsum, hP10010100]
    have hsimp : p * (1 - 2 * p) - (1 - 2 * p) ^ 2 = (1 - 2 * p) * (3 * p - 1) := by ring
    simpa [hsimp] using this

  -- Step B: compute `P(10100100) = (1-p)P(00100)`.
  have hP10100100' : prob μ (cyl 0 w10100100) = (1 - p) * (p ^ 2 - 5 * p + 2) := by
    have hshift : prob μ (cyl 0 w10100100) = prob μ (cyl 0 w010100100) :=
      prob_w10100100_eq_prob_w010100100 (μ := μ) hstat
    have hsep :
        ∀ i : Fin 1, ∀ j : Fin 5,
          Int.natAbs ((0 + Int.ofNat i.1) - (4 + Int.ofNat j.1)) > 3 := by
      native_decide
    have hind :
        prob μ (cyl 0 b0 ∩ cyl 4 w00100) = prob μ (cyl 0 b0) * prob μ (cyl 4 w00100) := by
      simpa using
          (KDependent.prob_inter_cyl_eq_mul (μ := μ) (k := 3) (m := 1) (n := 5) (a := 0) (b := 4)
          hdep hsep b0 w00100)
    have hs_w00100 : prob μ (cyl 4 w00100) = prob μ (cyl 0 w00100) := by
      simpa using
        (Stationary.prob_cyl_add_nat (μ := μ) hstat (a := 0) (s := 4) (w := w00100))
    have hb0 : prob μ (cyl 0 b0) = 1 - p := by
      have hb0' : prob μ (cyl 0 b0) = 1 - prob μ (cyl 0 b1) := prob_b0 (μ := μ)
      simpa [p] using hb0'
    have hset : cyl 0 w010100100 = cyl 0 b0 ∩ cyl 4 w00100 := cyl_w010100100_eq_inter
    calc
      prob μ (cyl 0 w10100100) = prob μ (cyl 0 w010100100) := hshift
      _ = prob μ (cyl 0 b0 ∩ cyl 4 w00100) := by simpa [hset]
      _ = prob μ (cyl 0 b0) * prob μ (cyl 4 w00100) := hind
      _ = (1 - p) * (p ^ 2 - 5 * p + 2) := by simp [hb0, hs_w00100, ha]

  -- Combine the two computations.
  have : (1 - 2 * p) * (3 * p - 1) = (1 - p) * (p ^ 2 - 5 * p + 2) := by
    simpa [hP10100100] using hP10100100'
  simpa [p] using this

theorem no_stationary_threeDependent (μ : Measure State) [IsProbabilityMeasure μ]
    (hstat : Stationary μ) (hdep : KDependent 3 μ) : False := by
  set p : ℝ := prob μ (cyl 0 b1)
  have hp : 3 * p ^ 2 - 6 * p + 2 = 0 := by
    simpa [p] using (quadratic_of_len6 (μ := μ) hstat hdep)
  have hstar :
      (1 - 2 * p) * (3 * p - 1) = (1 - p) * (p ^ 2 - 5 * p + 2) := by
    simpa [p] using (star_identity (μ := μ) hstat hdep)
  exact no_k3_kernel p hp hstar

end

end Model

end FiniteDependence.MIS
