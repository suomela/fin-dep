import FiniteDependence.Coloring.Words
import Mathlib.Data.Int.Interval
import Mathlib.Tactic

/-!
# Integer intervals as index types for finite words

To build the two-sided process on `ℤ`, we frequently move between:

* a finite word `Word q n := Fin n → Fin q`;
* an assignment of colors to an integer interval `[a, a+n)` represented as a function
  `IcoIdx a n → Fin q`, where `IcoIdx a n` is the type of elements of the finset
  `Finset.Ico a (a+n)`.

This file provides the basic equivalences and restriction lemmas needed for the projective
construction.
-/

namespace FiniteDependence.Coloring

namespace Word

/-- The type of indices in the integer interval `[a, a+n)`. -/
abbrev IcoIdx (a : ℤ) (n : ℕ) : Finset ℤ := (Finset.Ico a (a + n : ℤ))

instance (a : ℤ) : IsEmpty (IcoIdx a 0) := by
  refine ⟨?_⟩
  intro x
  have hx : a ≤ (x : ℤ) ∧ (x : ℤ) < a := by
    simpa [IcoIdx] using (Finset.mem_Ico).1 x.2
  exact (not_lt_of_ge hx.1 hx.2).elim

/-- An order-preserving equivalence `Fin n ≃ IcoIdx a n` given by `k ↦ a + k`. -/
noncomputable def equivIco (a : ℤ) : ∀ n : ℕ, Fin n ≃ IcoIdx a n
  | 0 =>
      (Equiv.equivEmpty (Fin 0)).trans (Equiv.equivEmpty (IcoIdx a 0)).symm
  | n + 1 =>
      { toFun := fun k =>
          ⟨a + k.1, by
            have hk : (k.1 : ℤ) < (n + 1 : ℤ) := by exact_mod_cast k.2
            have hk0 : (0 : ℤ) ≤ (k.1 : ℤ) := by exact_mod_cast (Nat.zero_le k.1)
            refine (Finset.mem_Ico).2 ?_
            constructor
            · exact le_add_of_nonneg_right hk0
            · simpa using add_lt_add_left hk a⟩
        invFun := fun i =>
          ⟨(i.1 - a).toNat, by
            have hi : a ≤ i.1 ∧ i.1 < a + (n + 1 : ℤ) := by
              simpa [IcoIdx] using (Finset.mem_Ico).1 i.2
            have hlt : i.1 - a < (n + 1 : ℤ) := (sub_lt_iff_lt_add').2 hi.2
            have hn0 : (n + 1 : ℕ) ≠ 0 := by simp
            exact (Int.toNat_lt_of_ne_zero (m := i.1 - a) hn0).2 hlt⟩
        left_inv := by
          intro k
          apply Fin.ext
          have hk0 : (0 : ℤ) ≤ (k.1 : ℤ) := by exact_mod_cast (Nat.zero_le k.1)
          have hk_toNat : ((k.1 : ℤ).toNat) = k.1 := by
            apply Int.ofNat.inj
            simp
          simp [hk_toNat, sub_eq_add_neg, add_assoc]
        right_inv := by
          intro i
          apply Subtype.ext
          have hi : a ≤ i.1 := (Finset.mem_Ico).1 i.2 |>.1
          have hnonneg : 0 ≤ i.1 - a := sub_nonneg.2 hi
          have hz : ((i.1 - a).toNat : ℤ) = i.1 - a := Int.toNat_of_nonneg hnonneg
          calc
            a + (Int.ofNat ((i.1 - a).toNat)) = a + ((i.1 - a).toNat : ℤ) := by rfl
            _ = a + (i.1 - a) := by simp [hz]
            _ = i.1 := by abel }

/-- Transport a word `w : Word q n` to an assignment on `[a, a+n)`. -/
noncomputable def wordToIco {q : ℕ} (a : ℤ) (n : ℕ) (w : Word q n) : (IcoIdx a n → Fin q) :=
  fun i => w ((equivIco a n).symm i)

/-- Transport an interval assignment on `[a, a+n)` back to a word of length `n`. -/
noncomputable def icoToWord {q : ℕ} (a : ℤ) (n : ℕ) (f : IcoIdx a n → Fin q) : Word q n :=
  fun k => f ((equivIco a n) k)

lemma icoToWord_wordToIco {q : ℕ} (a : ℤ) (n : ℕ) (w : Word q n) :
    icoToWord (q := q) a n (wordToIco (q := q) a n w) = w := by
  funext k
  simp [icoToWord, wordToIco]

lemma wordToIco_icoToWord {q : ℕ} (a : ℤ) (n : ℕ) (f : IcoIdx a n → Fin q) :
    wordToIco (q := q) a n (icoToWord (q := q) a n f) = f := by
  funext i
  simp [icoToWord, wordToIco]

/-! ## Interval inclusions and induced maps -/

/-!
## A shift function with definitional base case

Lean's expression `a + 0` is not definitionally equal to `a` when `a : ℤ`. When working with
dependent types such as `IcoIdx (a + l) n`, this can lead to awkward type casts in the base case
`l = 0`.

We therefore define an auxiliary "integer shift" `shiftInt a l` by recursion, so that
`shiftInt a 0 = a` definitionally and `shiftInt a (l+1) = shiftInt (a+1) l`. We also prove that
`shiftInt a l = a + l`.
-/

/-- Shift an integer by a natural number (recursive definition with `shiftInt a 0 = a`
definitionally). -/
def shiftInt (a : ℤ) : ℕ → ℤ
  | 0 => a
  | l + 1 => shiftInt (a + 1) l

@[simp] lemma shiftInt_zero (a : ℤ) : shiftInt a 0 = a := rfl

@[simp] lemma shiftInt_succ (a : ℤ) (l : ℕ) : shiftInt a (l + 1) = shiftInt (a + 1) l := rfl

lemma shiftInt_eq_add (a : ℤ) : ∀ l : ℕ, shiftInt a l = a + l
  | 0 => by simp [shiftInt]
  | l + 1 => by
      -- shift by one, then apply the inductive hypothesis
      simp [shiftInt, shiftInt_eq_add (a + 1) l, add_left_comm, add_comm]

lemma Ico_subset_Ico_succ (a : ℤ) (n : ℕ) : IcoIdx a n ⊆ IcoIdx a (n + 1) := by
  intro x hx
  have hx' : a ≤ (x : ℤ) ∧ (x : ℤ) < a + (n : ℤ) := by
    simpa [IcoIdx] using (Finset.mem_Ico).1 hx
  have hle : a + (n : ℤ) ≤ a + (n + 1 : ℤ) := by
    have : (n : ℤ) ≤ (n + 1 : ℤ) := by exact_mod_cast (Nat.le_succ n)
    linarith
  have hlt : (x : ℤ) < a + (n + 1 : ℤ) := lt_of_lt_of_le hx'.2 hle
  exact (Finset.mem_Ico).2 ⟨hx'.1, hlt⟩

/-- The inclusion `[a, a+n) ↪ [a, a+(n+1))`. -/
noncomputable def inclIco (a : ℤ) (n : ℕ) : IcoIdx a n → IcoIdx a (n + 1) :=
  fun x => ⟨x.1, Ico_subset_Ico_succ a n x.2⟩

lemma equivIco_symm_incl_toFun_castSucc (a : ℤ) (n : ℕ) (k : Fin n) :
    (equivIco a (n + 1)).symm (inclIco a n ((equivIco a n) k)) = Fin.castSucc k := by
  classical
  cases n with
  | zero =>
      exact k.elim0
  | succ n =>
      apply Fin.ext
      have hk0 : (0 : ℤ) ≤ (k.1 : ℤ) := by exact_mod_cast (Nat.zero_le k.1)
      have hk_toNat : ((k.1 : ℤ).toNat) = k.1 := by
        apply Int.ofNat.inj
        simp
      simp [equivIco, inclIco, hk_toNat, sub_eq_add_neg, add_assoc]

lemma Ico_succ_subset (a : ℤ) (n : ℕ) : IcoIdx (a + 1) n ⊆ IcoIdx a (n + 1) := by
  intro x hx
  have hx' : a + 1 ≤ (x : ℤ) ∧ (x : ℤ) < a + 1 + (n : ℤ) := by
    simpa [IcoIdx, add_assoc] using (Finset.mem_Ico).1 hx
  have hle : a ≤ (x : ℤ) := le_trans (by linarith) hx'.1
  have hlt : (x : ℤ) < a + (n + 1 : ℤ) := by
    simpa [add_assoc, add_left_comm, add_comm] using hx'.2
  exact (Finset.mem_Ico).2 ⟨hle, hlt⟩

lemma Ico_subset_Ico_add (a : ℤ) (n m : ℕ) : IcoIdx a n ⊆ IcoIdx a (n + m) := by
  intro x hx
  have hx' : a ≤ x ∧ x < a + (n : ℤ) := by
    simpa [IcoIdx] using (Finset.mem_Ico).1 hx
  have hle : a + (n : ℤ) ≤ a + (n + m : ℤ) := by
    have : (n : ℤ) ≤ (n + m : ℤ) := by exact_mod_cast Nat.le_add_right n m
    linarith
  have hlt : x < a + (n + m : ℤ) := lt_of_lt_of_le hx'.2 hle
  exact (Finset.mem_Ico).2 ⟨hx'.1, hlt⟩

lemma Ico_shift_subset (a : ℤ) (l n : ℕ) : IcoIdx (a + l) n ⊆ IcoIdx a (l + n) := by
  intro x hx
  have hx' : a + l ≤ x ∧ x < a + l + (n : ℤ) := by
    simpa [IcoIdx, add_assoc] using (Finset.mem_Ico).1 hx
  refine (Finset.mem_Ico).2 ?_
  constructor
  · exact le_trans (by linarith) hx'.1
  ·
    have hle : a + l + (n : ℤ) ≤ a + (l + n : ℤ) := by
      -- purely associative rewriting
      simp [add_assoc]
    exact lt_of_lt_of_le hx'.2 hle

lemma Ico_subinterval_subset (a : ℤ) (l n r : ℕ) :
    IcoIdx (a + l) n ⊆ IcoIdx a (l + n + r) := by
  intro x hx
  have hx' : a + l ≤ x ∧ x < a + l + (n : ℤ) := by
    simpa [IcoIdx, add_assoc] using (Finset.mem_Ico).1 hx
  refine (Finset.mem_Ico).2 ?_
  constructor
  · exact le_trans (by linarith) hx'.1
  ·
    have hle : a + l + (n : ℤ) ≤ a + (l + n + r : ℤ) := by
      -- `a + l + n = a + (l+n)` and `l+n ≤ l+n+r`.
      have hln : ((l + n : ℕ) : ℤ) ≤ (l + n + r : ℤ) := by
        exact_mod_cast Nat.le_add_right (l + n) r
      have h₂ : a + ((l + n) : ℤ) ≤ a + (l + n + r : ℤ) := by
        -- `add_le_add_left` adds `a` on the right; commute to match the goal.
        have h₂' : ((l + n : ℕ) : ℤ) ≤ (l + n + r : ℤ) := by
          exact hln
        linarith
      -- Rewrite `a + l + n` as `a + (l+n)` to conclude.
      have h₂'' : a + l + (n : ℤ) ≤ a + (l + n + r : ℤ) := by
        linarith
      exact h₂''
    exact lt_of_lt_of_le hx'.2 hle

/-- The inclusion `[a+1, a+1+n) ↪ [a, a+(n+1))`. -/
noncomputable def inclIco_succ (a : ℤ) (n : ℕ) : IcoIdx (a + 1) n → IcoIdx a (n + 1) :=
  fun x => ⟨x.1, Ico_succ_subset a n x.2⟩

lemma equivIco_symm_incl_succ_toFun (a : ℤ) (n : ℕ) (k : Fin n) :
    (equivIco a (n + 1)).symm (inclIco_succ a n ((equivIco (a + 1) n) k)) = Fin.succ k := by
  classical
  cases n with
  | zero =>
      exact k.elim0
  | succ n =>
      apply Fin.ext
      have hab : (a + (1 + ((k.1 : ℤ) + -a)) : ℤ) = (k.1 : ℤ) + 1 := by
        abel
      have hkpos : 0 ≤ (k.1 : ℤ) + 1 := by
        have : (0 : ℤ) ≤ (k.1 : ℤ) := by exact_mod_cast (Nat.zero_le k.1)
        linarith
      have hk_toNat : (((k.1 : ℤ) + 1).toNat) = k.1 + 1 := by
        apply Int.ofNat.inj
        simp
      simp [equivIco, inclIco_succ, hab, hk_toNat, sub_eq_add_neg, add_assoc]

/-! ## Word truncations and restriction lemmas -/

/-- Drop the last letter of a word. -/
noncomputable def initWord {q : ℕ} {n : ℕ} (w : Word q (n + 1)) : Word q n :=
  fun k => w k.castSucc

/-- Drop the first letter of a word. -/
noncomputable def tailWord {q : ℕ} {n : ℕ} (w : Word q (n + 1)) : Word q n :=
  fun k => w k.succ

lemma icoToWord_restrict_wordToIco_init {q : ℕ} (a : ℤ) (n : ℕ) (w : Word q (n + 1)) :
    icoToWord (q := q) a n
        (Finset.restrict₂ (π := fun _ : ℤ => Fin q) (Ico_subset_Ico_succ a n)
          (wordToIco (q := q) a (n + 1) w))
      = initWord (q := q) (n := n) w := by
  funext k
  simp [icoToWord, wordToIco, initWord]
  change w ((equivIco a (n + 1)).symm (inclIco a n ((equivIco a n) k))) = _
  simp [equivIco_symm_incl_toFun_castSucc]

lemma icoToWord_restrict_wordToIco_tail {q : ℕ} (a : ℤ) (n : ℕ) (w : Word q (n + 1)) :
    icoToWord (q := q) (a + 1) n
        (Finset.restrict₂ (π := fun _ : ℤ => Fin q) (Ico_succ_subset a n)
          (wordToIco (q := q) a (n + 1) w))
      = tailWord (q := q) (n := n) w := by
  funext k
  simp [icoToWord, wordToIco, tailWord]
  change w ((equivIco a (n + 1)).symm (inclIco_succ a n ((equivIco (a + 1) n) k))) = _
  simp [equivIco_symm_incl_succ_toFun]

/-! ## Finsets of one-letter extensions -/

/-- The finset of `snoc` extensions of a word. -/
noncomputable def snocSet {q : ℕ} {n : ℕ} (x : Word q n) : Finset (Word q (n + 1)) :=
  Finset.univ.image (fun a : Fin q => snoc x a)

lemma mem_snocSet_iff {q : ℕ} {n : ℕ} (x : Word q n) (w : Word q (n + 1)) :
    w ∈ snocSet (q := q) x ↔ initWord (q := q) (n := n) w = x := by
  classical
  constructor
  · intro hw
    rcases Finset.mem_image.1 hw with ⟨a, _ha, rfl⟩
    funext k
    simp [initWord]
  · intro hw
    refine Finset.mem_image.2 ?_
    refine ⟨w (Fin.last n), Finset.mem_univ _, ?_⟩
    funext i
    refine Fin.lastCases ?_ (fun j => ?_) i
    · simp
    ·
      have : x j = w j.castSucc := by
        simpa [initWord] using (congrArg (fun t : Word q n => t j) hw).symm
      simp [this]

/-- The finset of `cons` extensions of a word. -/
noncomputable def consSet {q : ℕ} {n : ℕ} (x : Word q n) : Finset (Word q (n + 1)) :=
  Finset.univ.image (fun a : Fin q => cons a x)

lemma mem_consSet_iff {q : ℕ} {n : ℕ} (x : Word q n) (w : Word q (n + 1)) :
    w ∈ consSet (q := q) x ↔ tailWord (q := q) (n := n) w = x := by
  classical
  constructor
  · intro hw
    rcases Finset.mem_image.1 hw with ⟨a, _ha, rfl⟩
    funext k
    simp [tailWord]
  · intro hw
    refine Finset.mem_image.2 ?_
    refine ⟨w 0, Finset.mem_univ _, ?_⟩
    funext i
    refine Fin.cases ?_ (fun j => ?_) i
    · simp
    ·
      have : x j = w j.succ := by
        simpa [tailWord] using (congrArg (fun t : Word q n => t j) hw).symm
      simp [this]

end Word

end FiniteDependence.Coloring
