import Mathlib.Data.Fin.Tuple.Basic
import Mathlib.Data.Fin.SuccPred

/-!
# Finite words and operations

We model a word of length `n` over an alphabet of size `q` as a function `Fin n → Fin q`.
This file provides basic operations (deletion, concatenation) and the predicate of being a
proper coloring (no equal adjacent letters).
-/

namespace FiniteDependence.Coloring

/-- A word of length `n` over `q` colors. -/
abbrev Word (q n : ℕ) : Type := Fin n → Fin q

namespace Word

variable {q m n : ℕ}

/-- Cast a word along an equality of lengths. -/
def cast {m n : ℕ} (h : m = n) (x : Word q m) : Word q n :=
  fun i => x (i.cast h.symm)

@[simp] lemma cast_rfl (x : Word q m) : cast (q := q) (m := m) (n := m) rfl x = x := by
  ext i
  rfl

/-- A word is a proper coloring if adjacent letters are different. -/
def IsProper : ∀ {n : ℕ}, Word q n → Prop
  | 0, _ => True
  | 1, _ => True
  | n + 2, x => ∀ i : Fin (n + 1), x i.castSucc ≠ x i.succ

@[simp] lemma isProper_cast_iff {m n : ℕ} (h : m = n) (x : Word q m) :
    IsProper (cast (q := q) h x) ↔ IsProper x := by
  cases h
  simp

lemma castSucc_succ {n : ℕ} (i : Fin n) : i.castSucc.succ = (i.succ).castSucc := by
  ext
  simp

instance instDecidableIsProper {n : ℕ} (x : Word q n) : Decidable (IsProper x) := by
  cases n with
  | zero =>
    simp [IsProper]
    infer_instance
  | succ n =>
    cases n with
    | zero =>
      simp [IsProper]
      infer_instance
    | succ n =>
      -- In this case, `IsProper` is a finite `∀` of decidable inequalities.
      simp [IsProper]
      infer_instance

/-- Delete the letter at position `i`. -/
def erase (x : Word q (n + 1)) (i : Fin (n + 1)) : Word q n :=
  fun j => x (i.succAbove j)

/-- Append one letter at the end. -/
def snoc (x : Word q n) (a : Fin q) : Word q (n + 1) :=
  Fin.snoc x a

@[simp] lemma snoc_last (x : Word q n) (a : Fin q) :
    snoc x a (Fin.last n) = a := by
  simp [snoc]

@[simp] lemma snoc_castSucc (x : Word q n) (a : Fin q) (i : Fin n) :
    snoc x a i.castSucc = x i := by
  simp [snoc]

/-- Prepend one letter at the beginning. -/
def cons (a : Fin q) (x : Word q n) : Word q (n + 1) :=
  Fin.cons a x

@[simp] lemma cons_zero (a : Fin q) (x : Word q n) :
    cons a x 0 = a := by
  simp [cons]

@[simp] lemma cons_succ (a : Fin q) (x : Word q n) (i : Fin n) :
    cons a x i.succ = x i := by
  simp [cons]

lemma isProper_of_isProper_snoc {n : ℕ} (x : Word q (n + 1)) (a : Fin q)
    (hx : IsProper (snoc x a)) : IsProper x := by
  cases n with
  | zero =>
    simp [IsProper]
  | succ n =>
    intro i hEq
    -- Use the condition in the longer word at the embedded index `i.castSucc`.
    have h := hx i.castSucc
    -- Produce a contradiction by turning `hEq : x i.castSucc = x i.succ` into an equality of
    -- the corresponding letters in `snoc x a`.
    refine h ?_
    calc
      snoc x a (i.castSucc.castSucc) = x i.castSucc := by
        exact snoc_castSucc (x := x) (a := a) (i := i.castSucc)
      _ = x i.succ := hEq
      _ = snoc x a (i.succ.castSucc) := by
        exact (snoc_castSucc (x := x) (a := a) (i := i.succ)).symm
      _ = snoc x a (i.castSucc.succ) := by
            -- `i.castSucc.succ = i.succ.castSucc`.
            rw [castSucc_succ (i := i)]

lemma not_isProper_snoc_self {n : ℕ} (x : Word q (n + 1)) :
    ¬ IsProper (snoc x (x (Fin.last n))) := by
  intro hx
  have h := hx (Fin.last n)
  simp [snoc] at h

lemma isProper_snoc_iff {n : ℕ} (x : Word q (n + 1)) (a : Fin q) :
    IsProper (snoc x a) ↔ IsProper x ∧ x (Fin.last n) ≠ a := by
  constructor
  · intro hx
    refine ⟨isProper_of_isProper_snoc x a hx, ?_⟩
    have h := hx (Fin.last n)
    simpa [snoc] using h
  · rintro ⟨hx, ha⟩
    cases n with
    | zero =>
      intro i
      -- Length `2`: only the boundary constraint exists.
      have : i = 0 := Fin.eq_zero i
      subst this
      simpa [IsProper, snoc] using ha
    | succ n =>
      intro i
      induction i using Fin.lastCases with
      | last =>
        simpa [snoc] using ha
      | cast i =>
        have h' : snoc x a (i.castSucc.castSucc) ≠ snoc x a (i.succ.castSucc) := by
          intro hEq
          have hEq' := hEq
          -- Rewrite both sides using `snoc_castSucc`.
          rw [snoc_castSucc (x := x) (a := a) (i := i.castSucc)] at hEq'
          rw [snoc_castSucc (x := x) (a := a) (i := i.succ)] at hEq'
          exact (hx i) hEq'
        have h'' := h'
        -- Rewrite `i.succ.castSucc` to `i.castSucc.succ`.
        rw [(castSucc_succ (i := i)).symm] at h''
        exact h''

/-- Concatenate two words. -/
def append (x : Word q m) (y : Word q n) : Word q (m + n) :=
  Fin.append x y

/-- Insert a letter between two words. -/
def insert1 (x : Word q m) (a : Fin q) (y : Word q n) : Word q (m + 1 + n) :=
  append (snoc x a) y

/-- Insert two letters between two words. -/
def insert2 (x : Word q m) (a b : Fin q) (y : Word q n) : Word q (m + 2 + n) :=
  append (snoc (snoc x a) b) y

/-! ## Properness of concatenation -/

lemma isProper_succ_iff {m : ℕ} (x : Word q (m + 1)) :
    IsProper x ↔ ∀ i : Fin m, x i.castSucc ≠ x i.succ := by
  cases m <;> simp [IsProper]

lemma isProper_append_iff {m n : ℕ} (x : Word q (m + 1)) (y : Word q (n + 1)) :
    IsProper (append x y) ↔ IsProper x ∧ IsProper y ∧ x (Fin.last m) ≠ y 0 := by
  classical
  -- Rewrite each properness predicate in the uniform `∀ i : Fin _` form.
  have hx_succ :
      IsProper x ↔ ∀ i : Fin m, x i.castSucc ≠ x i.succ :=
    isProper_succ_iff (q := q) (x := x)
  have hy_succ :
      IsProper y ↔ ∀ i : Fin n, y i.castSucc ≠ y i.succ :=
    isProper_succ_iff (q := q) (x := y)
  have hxy_succ :
      IsProper (append x y)
        ↔ ∀ i : Fin ((m + 1) + n), (append x y) i.castSucc ≠ (append x y) i.succ := by
    -- `append x y` has length `(m + 1) + (n + 1) = ((m + 1) + n) + 1`.
    simpa [Nat.add_assoc] using
      (isProper_succ_iff (q := q)
        (x := append (q := q) (m := m + 1) (n := n + 1) x y) (m := (m + 1) + n))

  constructor
  · intro h
    have h' : ∀ i : Fin ((m + 1) + n), (append x y) i.castSucc ≠ (append x y) i.succ :=
      (hxy_succ.mp h)

    -- Properness of `x`.
    have hx' : ∀ i : Fin m, x i.castSucc ≠ x i.succ := by
      intro i
      -- Use the properness constraint in `append x y` at the corresponding left index.
      have hi := h' (Fin.castAdd n i.castSucc)
      -- Rewrite both sides to lie in the left block.
      have h_castSucc :
          (Fin.castAdd n i.castSucc).castSucc = Fin.castAdd (n + 1) i.castSucc := by
        simpa using (Fin.castSucc_castAdd (m := n) (i := i.castSucc))
      have h_succ :
          (Fin.castAdd n i.castSucc).succ = Fin.castAdd (n + 1) i.succ := by
        apply Fin.ext
        simp
      -- Now `simp` using the explicit index forms.
      simpa [Word.append, h_castSucc, h_succ] using hi

    -- Properness of `y`.
    have hy' : ∀ j : Fin n, y j.castSucc ≠ y j.succ := by
      intro j
      have hj := h' (Fin.natAdd (m + 1) j)
      have h_castSucc :
          (Fin.natAdd (m + 1) j).castSucc = Fin.natAdd (m + 1) j.castSucc := by
        apply Fin.ext
        simp
      have h_succ :
          (Fin.natAdd (m + 1) j).succ = Fin.natAdd (m + 1) j.succ := by
        -- `succ (natAdd _ _)` is definitional, but `Fin.ext` keeps this robust.
        apply Fin.ext
        simp [Nat.add_assoc]
      simpa [Word.append, h_castSucc, h_succ] using hj

    -- Boundary inequality.
    have hbd := h' (Fin.castAdd n (Fin.last m))
    have h_castSucc :
        (Fin.castAdd n (Fin.last m)).castSucc = Fin.castAdd (n + 1) (Fin.last m) := by
      simpa using (Fin.castSucc_castAdd (m := n) (i := Fin.last m))
    have h_succ :
        (Fin.castAdd n (Fin.last m)).succ = Fin.natAdd (m + 1) (0 : Fin (n + 1)) := by
      apply Fin.ext
      simp
    have hbd' : x (Fin.last m) ≠ y 0 := by
      simpa [Word.append, h_castSucc, h_succ] using hbd

    refine ⟨hx_succ.mpr hx', hy_succ.mpr hy', hbd'⟩

  · rintro ⟨hx, hy, hbd⟩
    -- Put the hypotheses in the `∀ i : Fin _` form.
    have hx' : ∀ i : Fin m, x i.castSucc ≠ x i.succ := hx_succ.mp hx
    have hy' : ∀ j : Fin n, y j.castSucc ≠ y j.succ := hy_succ.mp hy

    -- Prove `append x y` is proper by checking each adjacency index.
    have h' : ∀ i : Fin ((m + 1) + n), (append x y) i.castSucc ≠ (append x y) i.succ := by
      intro i
      -- Split `i` into the left block (including the boundary) and the right block.
      induction i using Fin.addCases with
      | left i =>
          -- Here `i : Fin (m + 1)` and the original index is `Fin.castAdd n i`.
          induction i using Fin.lastCases with
          | cast i =>
              -- Internal adjacency inside `x`.
              have hi := hx' i
              have h_castSucc :
                  (Fin.castAdd n i.castSucc).castSucc = Fin.castAdd (n + 1) i.castSucc := by
                simpa using (Fin.castSucc_castAdd (m := n) (i := i.castSucc))
              have h_succ :
                  (Fin.castAdd n i.castSucc).succ = Fin.castAdd (n + 1) i.succ := by
                apply Fin.ext
                simp
              simpa [Word.append, h_castSucc, h_succ] using hi
          | last =>
              -- The boundary adjacency between `x (last m)` and `y 0`.
              have h_castSucc :
                  (Fin.castAdd n (Fin.last m)).castSucc = Fin.castAdd (n + 1) (Fin.last m) := by
                simpa using (Fin.castSucc_castAdd (m := n) (i := Fin.last m))
              have h_succ :
                  (Fin.castAdd n (Fin.last m)).succ = Fin.natAdd (m + 1) (0 : Fin (n + 1)) := by
                apply Fin.ext
                simp
              simpa [Word.append, h_castSucc, h_succ] using hbd
      | right j =>
          -- Here `j : Fin n` and the original index is `Fin.natAdd (m + 1) j`.
          have hj := hy' j
          have h_castSucc :
              (Fin.natAdd (m + 1) j).castSucc = Fin.natAdd (m + 1) j.castSucc := by
            apply Fin.ext
            simp
          have h_succ :
              (Fin.natAdd (m + 1) j).succ = Fin.natAdd (m + 1) j.succ := by
            apply Fin.ext
            simp [Nat.add_assoc]
          simpa [Word.append, h_castSucc, h_succ] using hj

    exact hxy_succ.mpr h'

lemma isProper_append_left {m n : ℕ} (x : Word q (m + 1)) (y : Word q (n + 1))
    (h : IsProper (append x y)) : IsProper x :=
  (isProper_append_iff (x := x) (y := y)).1 h |>.1

lemma isProper_append_right {m n : ℕ} (x : Word q (m + 1)) (y : Word q (n + 1))
    (h : IsProper (append x y)) : IsProper y :=
  (isProper_append_iff (x := x) (y := y)).1 h |>.2.1

lemma isProper_append_of_isProper {m n : ℕ} (x : Word q (m + 1)) (y : Word q (n + 1))
    (hx : IsProper x) (hy : IsProper y) (hxy : x (Fin.last m) ≠ y 0) :
    IsProper (append x y) :=
  (isProper_append_iff (x := x) (y := y)).2 ⟨hx, hy, hxy⟩

lemma not_isProper_append_of_eq_boundary {m n : ℕ} (x : Word q (m + 1)) (y : Word q (n + 1))
    (hxy : x (Fin.last m) = y 0) : ¬ IsProper (append x y) := by
  intro h
  exact (isProper_append_iff (x := x) (y := y)).1 h |>.2.2 (by simp [hxy])

lemma not_isProper_append_left_of_not_isProper {m n : ℕ} (x : Word q (m + 1)) (y : Word q (n + 1))
    (hx : ¬ IsProper x) : ¬ IsProper (append x y) := by
  intro h
  exact hx (isProper_append_left (x := x) (y := y) h)

lemma not_isProper_append_right_of_not_isProper {m n : ℕ} (x : Word q (m + 1)) (y : Word q (n + 1))
    (hy : ¬ IsProper y) : ¬ IsProper (append x y) := by
  intro h
  exact hy (isProper_append_right (x := x) (y := y) h)

@[simp] lemma erase_snoc_last (x : Word q n) (a : Fin q) :
    erase (snoc x a) (Fin.last n) = x := by
  ext i
  simp [erase, snoc]

@[simp] lemma erase_snoc_castSucc (x : Word q (n + 1)) (a : Fin q) (i : Fin (n + 1)) :
    erase (snoc x a) i.castSucc = snoc (erase x i) a := by
  ext j
  -- Split on whether `j` is the last index.
  induction j using Fin.lastCases with
  | last =>
    simp [erase, snoc]
  | cast j =>
    simp [erase, snoc]

@[simp] lemma snoc_erase_last (x : Word q (n + 1)) :
    snoc (erase x (Fin.last n)) (x (Fin.last n)) = x := by
  ext i
  induction i using Fin.lastCases with
  | last =>
    simp [snoc]
  | cast i =>
    simp [erase, snoc]

@[simp] lemma erase_castSucc_last {n : ℕ} (x : Word q (n + 2)) (i : Fin (n + 1)) :
    erase (q := q) (n := n + 1) x i.castSucc (Fin.last n) = x (Fin.last (n + 1)) := by
  have hne : (i.castSucc : Fin (n + 2)) ≠ Fin.last (n + 1) :=
    Fin.ne_of_lt i.castSucc_lt_last
  -- `succAbove` maps the last index to the last index when we delete a non-last position.
  simp [erase, hne]

@[simp] lemma erase_succ_zero {n : ℕ} (x : Word q (n + 2)) (i : Fin (n + 1)) :
    erase (q := q) (n := n + 1) x i.succ 0 = x 0 := by
  have hlt : (Fin.castSucc (0 : Fin (n + 1))) < i.succ := by
    -- `0 < i.succ` and `castSucc 0 = 0`.
    simp [Fin.lt_def]
  simp [erase, Fin.succAbove_of_castSucc_lt _ _ hlt]

end Word

end FiniteDependence.Coloring
