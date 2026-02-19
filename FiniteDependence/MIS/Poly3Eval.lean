import FiniteDependence.MIS.Poly3Lawful
import Std.Data.TreeMap.Lemmas

namespace FiniteDependence.MIS

namespace Poly3

open Std
open scoped Std.TreeMap
open scoped BigOperators

/-!
Evaluation of `Poly3.Poly` into `ℝ`.

This is used to interpret the computable polynomial certificates (proved by `native_decide`)
as genuine real identities about probabilities.
-/

noncomputable section

def monomVal (p t u : ℝ) (m : Monom) : ℝ :=
  p ^ m.pExp * t ^ m.tExp * u ^ m.uExp

lemma monomVal_mul (p t u : ℝ) (a b : Monom) :
    monomVal p t u (Monom.mul a b) = monomVal p t u a * monomVal p t u b := by
  simp [monomVal, Monom.mul, pow_add, mul_assoc, mul_left_comm, mul_comm]

def evalTerm (p t u : ℝ) : Term → ℝ
  | (m, c) => (c : ℝ) * monomVal p t u m

def evalTerms (p t u : ℝ) (ts : List Term) : ℝ :=
  (ts.map (evalTerm p t u)).sum

def eval (p t u : ℝ) (a : Poly) : ℝ :=
  evalTerms p t u a.terms

lemma evalTerms_nil (p t u : ℝ) : evalTerms p t u [] = 0 := by
  simp [evalTerms]

lemma evalTerms_cons (p t u : ℝ) (x : Term) (xs : List Term) :
    evalTerms p t u (x :: xs) = evalTerm p t u x + evalTerms p t u xs := by
  simp [evalTerms]

lemma evalTerms_append (p t u : ℝ) (xs ys : List Term) :
    evalTerms p t u (xs ++ ys) = evalTerms p t u xs + evalTerms p t u ys := by
  simp [evalTerms, List.map_append, List.sum_append]

/-! ### `normalize` preserves evaluation -/

private def evalMap (p t u : ℝ) (m : Std.TreeMap Monom ℚ) : ℝ :=
  evalTerms p t u m.toList

private lemma toList_erase_eq_filter (m : Std.TreeMap Monom ℚ) (k : Monom) :
    (m.erase k).toList = m.toList.filter (fun p => decide (p.1 ≠ k)) := by
  classical
  -- `erase` and `filter (· ≠ k)` have the same lookups, hence are equivalent.
  have heq :
      (m.erase k) ~m (m.filter (fun a _ => decide (a ≠ k))) := by
    refine Std.TreeMap.Equiv.of_forall_constGet?_eq (t₁ := m.erase k)
      (t₂ := m.filter (fun a _ => decide (a ≠ k))) ?_
    intro a
    by_cases ha : a = k
    · subst ha
      simp
    · have hdec : decide (a ≠ k) = true := by
        simpa [decide_eq_true_eq] using ha
      have hdecEq : decide (a = k) = false := by
        -- `decide (a = k)` is false because `a ≠ k`.
        simpa [decide_eq_false_iff_not] using ha
      have hcmp : compare k a ≠ .eq := by
        intro hcmp
        apply ha
        -- `compare k a = .eq` implies `k = a`, hence `a = k`.
        exact (Std.LawfulEqOrd.eq_of_compare hcmp).symm
      -- For `a ≠ k`, `erase` leaves the entry, and the filter predicate is true.
      -- Unfold `Option.filter` explicitly to avoid rewriting loops.
      have hcmp' :
          ¬ (match compare k.pExp a.pExp with
              | .eq =>
                  match compare k.tExp a.tExp with
                  | .eq => compare k.uExp a.uExp
                  | o => o
              | o => o) = .eq := by
        simpa [compare_def] using hcmp
      cases h : m[a]? with
      | none =>
          simp [Std.TreeMap.getElem?_erase, Std.TreeMap.getElem?_filter', compare_def,
            hcmp', hdec, hdecEq, Option.filter, h]
      | some val =>
          -- In the `some` case, the lookup equality reduces to the fact that `compare k a ≠ .eq`,
          -- i.e. `hcmp'`.
          simpa [Std.TreeMap.getElem?_erase, Std.TreeMap.getElem?_filter', compare_def,
            hdec, hdecEq, Option.filter, h] using hcmp'
  -- Turn equivalence into a `toList` equality and use the `toList_filter` lemma.
  have hto : (m.erase k).toList = (m.filter (fun a _ => decide (a ≠ k))).toList :=
    Std.TreeMap.Equiv.toList_eq (t₁ := m.erase k) (t₂ := m.filter (fun a _ => decide (a ≠ k))) heq
  simpa [Std.TreeMap.toList_filter] using hto

private lemma evalMap_insert (p t u : ℝ) (m : Std.TreeMap Monom ℚ) (k : Monom) (v : ℚ) :
    evalMap p t u (m.insert k v) = evalMap p t u (m.erase k) + evalTerm p t u (k, v) := by
  classical
  -- `toList_insert_perm` + the explicit description of `erase` as a list filter.
  have hperm0 :
      (m.insert k v).toList.Perm (⟨k, v⟩ :: m.toList.filter (fun p => !decide (k = p.1))) := by
    simpa using (Std.TreeMap.toList_insert_perm (t := m) (k := k) (v := v))
  -- Rewrite the filter predicate to `decide (p.1 ≠ k)` to match `toList_erase_eq_filter`.
  have hpred : ∀ p ∈ m.toList, (!decide (k = p.1)) = decide (p.1 ≠ k) := by
    intro p _hp
    by_cases hk : p.1 = k
    · subst hk
      simp
    · have hk' : p.1 ≠ k := hk
      have hk2 : k ≠ p.1 := by
        intro h
        apply hk
        exact h.symm
      simp [hk, hk', hk2]
  have hfilterPred :
      m.toList.filter (fun p => !decide (k = p.1)) = m.toList.filter (fun p => decide (p.1 ≠ k)) := by
    simpa using (List.filter_congr (l := m.toList) (p := fun p => !decide (k = p.1))
      (q := fun p => decide (p.1 ≠ k)) hpred)
  have hfilter :
      m.toList.filter (fun p => !decide (k = p.1)) = (m.erase k).toList := by
    simpa [toList_erase_eq_filter, hfilterPred] using (toList_erase_eq_filter (m := m) (k := k)).symm

  -- Apply permutation invariance of sums.
  have hsum :
      (List.map (evalTerm p t u) (m.insert k v).toList).sum =
        (List.map (evalTerm p t u) (⟨k, v⟩ :: m.toList.filter (fun p => !decide (k = p.1)))).sum := by
    exact List.Perm.sum_eq (hperm0.map (fun q => evalTerm p t u q))

  -- Unfold evaluation and simplify.
  -- RHS sum = evalTerm (k,v) + sum over the filtered list, and that filtered list is `toList (erase k)`.
  have : evalMap p t u (m.insert k v) = evalTerm p t u (k, v) + evalMap p t u (m.erase k) := by
    -- Turn the `List.sum` statement into the `evalMap` statement.
    -- After rewriting the filtered list as `toList (erase k)`, the RHS is exactly `evalTerm + evalMap`.
    simp [evalMap, evalTerms, evalTerms_cons, hfilter] at hsum
    simpa [evalMap, evalTerms, add_comm, add_left_comm, add_assoc] using hsum

  simpa [add_comm, add_left_comm, add_assoc] using this

private lemma evalMap_addTermMap (p t u : ℝ) (m : Std.TreeMap Monom ℚ) (x : Term) :
    evalMap p t u (addTermMap m x) = evalMap p t u m + evalTerm p t u x := by
  classical
  rcases x with ⟨mono, coeff⟩
  by_cases hcoeff : coeff = 0
  · subst hcoeff
    simp [addTermMap, evalMap, evalTerms, evalTerm]
  · -- Nonzero coefficient: either insert, update, or cancel.
    cases hget : m.get? mono with
    | none =>
        -- Fresh insert.
        -- If `mono` is absent, erasing does nothing.
        have herase : evalMap p t u (m.erase mono) = evalMap p t u m := by
          -- Build equivalence from lookup equality, then use `toList_eq`.
          have hnone : m[mono]? = none := by simpa using hget
          have heq : (m.erase mono) ~m m := by
            refine Std.TreeMap.Equiv.of_forall_constGet?_eq (t₁ := m.erase mono) (t₂ := m) ?_
            intro k
            by_cases hk : k = mono
            · subst hk
              simp [Std.TreeMap.getElem?_erase_self, hnone]
            · have hcmp : compare mono k ≠ .eq := by
                intro hcmp
                apply hk
                exact (Std.LawfulEqOrd.eq_of_compare hcmp).symm
              -- For `k ≠ mono`, `erase` leaves the lookup unchanged.
              simp [Std.TreeMap.getElem?_erase, hcmp]
          have hto : (m.erase mono).toList = m.toList :=
            Std.TreeMap.Equiv.toList_eq (t₁ := m.erase mono) (t₂ := m) heq
          simp [evalMap, evalTerms, hto]
        -- Now `insert` adds exactly the new term.
        calc
          evalMap p t u (addTermMap m (mono, coeff))
              = evalMap p t u (m.insert mono coeff) := by
                  have hget' : m[mono]? = none := by simpa using hget
                  simp [addTermMap, hcoeff, hget']
          _ = evalMap p t u (m.erase mono) + evalTerm p t u (mono, coeff) := evalMap_insert (p := p) (t := t) (u := u) (m := m) (k := mono) (v := coeff)
          _ = evalMap p t u m + evalTerm p t u (mono, coeff) := by simpa [herase]
    | some c0 =>
        let c1 : ℚ := c0 + coeff

        -- `insert mono c0` does not change the map (extensional equality on lookups).
        have hmono : m[mono]? = some c0 := by simpa using hget
        have hinsert : evalMap p t u (m.insert mono c0) = evalMap p t u m := by
          have heq : m.insert mono c0 ~m m := by
            refine Std.TreeMap.Equiv.of_forall_constGet?_eq (t₁ := m.insert mono c0) (t₂ := m) ?_
            intro k
            by_cases hk : k = mono
            · subst hk
              simp [Std.TreeMap.getElem?_insert, hmono]
            · have hcmp : compare mono k ≠ .eq := by
                intro hcmp
                apply hk
                exact (Std.LawfulEqOrd.eq_of_compare hcmp).symm
              simp [Std.TreeMap.getElem?_insert, hcmp, hk]
          have hto : (m.insert mono c0).toList = m.toList :=
            Std.TreeMap.Equiv.toList_eq (t₁ := m.insert mono c0) (t₂ := m) heq
          simp [evalMap, evalTerms, hto]

        -- Decompose `evalMap m` into the erased part plus the `mono` contribution.
        have hdecomp :
            evalMap p t u m = evalMap p t u (m.erase mono) + evalTerm p t u (mono, c0) := by
          have hins :=
            evalMap_insert (p := p) (t := t) (u := u) (m := m) (k := mono) (v := c0)
          simpa [hinsert] using hins

        by_cases hc1 : c1 = 0
        · -- Cancellation: resulting map is `erase mono`.
          have hadd : addTermMap m (mono, coeff) = m.erase mono := by
            simp [addTermMap, hcoeff, hmono, c1, hc1]
          have hcoef : coeff = -c0 := by
            have : c0 + coeff = 0 := hc1
            linarith
          have hterm : evalTerm p t u (mono, coeff) = -evalTerm p t u (mono, c0) := by
            simp [evalTerm, hcoef, mul_assoc]
          have herase : evalMap p t u (m.erase mono) = evalMap p t u m + evalTerm p t u (mono, coeff) := by
            have : evalMap p t u (m.erase mono) = evalMap p t u m - evalTerm p t u (mono, c0) := by
              linarith [hdecomp]
            -- Substitute `evalTerm coeff = - evalTerm c0`.
            linarith [this, hterm]
          simpa [hadd] using herase
        · -- Non-cancelling update: insert `c1`.
          have hadd : addTermMap m (mono, coeff) = m.insert mono c1 := by
            simp [addTermMap, hcoeff, hmono, c1, hc1]
          have hnew :
              evalMap p t u (m.insert mono c1) =
                evalMap p t u (m.erase mono) + evalTerm p t u (mono, c1) :=
            evalMap_insert (p := p) (t := t) (u := u) (m := m) (k := mono) (v := c1)
          have hdiff :
              evalMap p t u (m.insert mono c1) =
                evalMap p t u m + (evalTerm p t u (mono, c1) - evalTerm p t u (mono, c0)) := by
            linarith [hnew, hdecomp]
          have hlin :
              evalTerm p t u (mono, c1) - evalTerm p t u (mono, c0) = evalTerm p t u (mono, coeff) := by
            -- `c1 = c0 + coeff` and `evalTerm` is linear in the coefficient.
            simp [evalTerm, c1, sub_eq_add_neg, add_mul, mul_assoc, mul_left_comm, mul_comm]
          simpa [hadd, hlin, sub_eq_add_neg, add_assoc, add_left_comm, add_comm] using hdiff

theorem eval_mk (p t u : ℝ) (ts : List Term) :
    eval p t u (mk ts) = evalTerms p t u ts := by
  classical
  -- Inductively compare the evaluation of the accumulator `TreeMap` to the sum of processed terms.
  have hfold :
      ∀ (l : List Term) (m : Std.TreeMap Monom ℚ),
        evalMap p t u (l.foldl addTermMap m) = evalMap p t u m + evalTerms p t u l := by
    intro l m
    induction l generalizing m with
    | nil =>
        simp [evalTerms_nil]
    | cons x xs ih =>
        have hx :=
          evalMap_addTermMap (p := p) (t := t) (u := u) (m := m) (x := x)
        calc
          evalMap p t u ((x :: xs).foldl addTermMap m)
              = evalMap p t u (xs.foldl addTermMap (addTermMap m x)) := by
                  simp [List.foldl]
          _ = evalMap p t u (addTermMap m x) + evalTerms p t u xs := by
                  simpa using (ih (m := addTermMap m x))
          _ = (evalMap p t u m + evalTerm p t u x) + evalTerms p t u xs := by
                  simpa [hx]
          _ = evalMap p t u m + (evalTerm p t u x + evalTerms p t u xs) := by
                  ac_rfl
          _ = evalMap p t u m + evalTerms p t u (x :: xs) := by
                  simp [evalTerms_cons, add_assoc]

  have hemptyToList : (({} : Std.TreeMap Monom ℚ).toList) = [] := by
    rfl
  have hempty : evalMap p t u ({} : Std.TreeMap Monom ℚ) = 0 := by
    simp [evalMap, evalTerms, hemptyToList]

  have h0 : evalMap p t u (ts.foldl addTermMap {}) = evalTerms p t u ts := by
    have := hfold ts ({} : Std.TreeMap Monom ℚ)
    simpa [hempty, evalTerms_nil, add_assoc] using this

  -- Unfold `mk` and `normalize`.
  simpa [eval, mk, normalize, evalMap] using h0

/-! ### Evaluation lemmas for the `Poly3` operations -/

@[simp] lemma ofNat_eq_const (n : Nat) : (OfNat.ofNat n : Poly) = const (n : ℚ) := by
  rfl

lemma eval_const (p t u : ℝ) (q : ℚ) :
    eval p t u (const q) = (q : ℝ) := by
  by_cases hq : q = 0
  · subst hq
    simp [const, eval, evalTerms]
  · simp [const, hq, eval, evalTerms, evalTerm, monomVal]

lemma eval_varP (p t u : ℝ) :
    eval p t u varP = p := by
  simp [varP, eval, evalTerms, evalTerm, monomVal]

lemma eval_varT (p t u : ℝ) :
    eval p t u varT = t := by
  simp [varT, eval, evalTerms, evalTerm, monomVal]

lemma eval_varU (p t u : ℝ) :
    eval p t u varU = u := by
  simp [varU, eval, evalTerms, evalTerm, monomVal]

lemma eval_add (p t u : ℝ) (a b : Poly) :
    eval p t u (a + b) = eval p t u a + eval p t u b := by
  change eval p t u (add a b) = eval p t u a + eval p t u b
  calc
    eval p t u (add a b)
        = evalTerms p t u (a.terms ++ b.terms) := by
            simp [add, eval_mk]
    _ = evalTerms p t u a.terms + evalTerms p t u b.terms := by
            simp [evalTerms_append]
    _ = eval p t u a + eval p t u b := by
            rfl

lemma eval_neg (p t u : ℝ) (a : Poly) :
    eval p t u (-a) = -eval p t u a := by
  change eval p t u (neg a) = -eval p t u a
  -- `neg` flips each coefficient, and `evalTerm` is linear in the coefficient.
  have hterm : ∀ x : Term, evalTerm p t u (x.1, -x.2) = -evalTerm p t u x := by
    intro x
    rcases x with ⟨m, c⟩
    simp [evalTerm, mul_assoc]
  have hterms :
      evalTerms p t u (a.terms.map (fun x => (x.1, -x.2))) = -evalTerms p t u a.terms := by
    induction a.terms with
    | nil =>
        simp [evalTerms_nil]
    | cons x xs ih =>
        simp [evalTerms_cons, hterm, ih, add_comm, add_left_comm, add_assoc]
  -- Unfold `neg` and apply `eval_mk`.
  calc
    eval p t u (neg a)
        = evalTerms p t u (a.terms.map (fun x => (x.1, -x.2))) := by
            simp [neg, eval_mk]
    _ = -evalTerms p t u a.terms := hterms
    _ = -eval p t u a := by
            rfl

lemma eval_sub (p t u : ℝ) (a b : Poly) :
    eval p t u (a - b) = eval p t u a - eval p t u b := by
  change eval p t u (sub a b) = eval p t u a - eval p t u b
  -- `sub a b = add a (neg b)` and `eval` respects `add/neg`.
  have hAdd : eval p t u (add a (neg b)) = eval p t u a + eval p t u (neg b) := by
    -- `add a (neg b)` is definitionally `a + neg b`.
    simpa using (eval_add (p := p) (t := t) (u := u) (a := a) (b := neg b))
  have hNeg : eval p t u (neg b) = -eval p t u b := by
    -- `neg b` is definitionally `-b`.
    simpa using (eval_neg (p := p) (t := t) (u := u) (a := b))
  -- Finish by rewriting.
  simp [sub, sub_eq_add_neg, hAdd, hNeg, add_assoc]

lemma eval_smul (p t u : ℝ) (q : ℚ) (a : Poly) :
    eval p t u (q • a) = (q : ℝ) * eval p t u a := by
  classical
  change eval p t u (smul q a) = (q : ℝ) * eval p t u a
  by_cases hq : q = 0
  · subst hq
    simp [smul, eval_const]
  · have hterm : ∀ x : Term, evalTerm p t u (x.1, q * x.2) = (q : ℝ) * evalTerm p t u x := by
      intro x
      rcases x with ⟨m, c⟩
      simp [evalTerm, mul_assoc, mul_left_comm, mul_comm]
    have hterms :
        evalTerms p t u (a.terms.map (fun x => (x.1, q * x.2))) =
          (q : ℝ) * evalTerms p t u a.terms := by
      induction a.terms with
      | nil =>
          simp [evalTerms_nil]
      | cons x xs ih =>
          simp [evalTerms_cons, hterm, ih, mul_add, add_comm, add_left_comm, add_assoc]
    -- Unfold `smul` and apply `eval_mk`.
    calc
      eval p t u (smul q a)
          = evalTerms p t u (a.terms.map (fun x => (x.1, q * x.2))) := by
              simp [smul, hq, eval_mk]
      _ = (q : ℝ) * evalTerms p t u a.terms := hterms
      _ = (q : ℝ) * eval p t u a := by
              rfl

lemma eval_mul (p t u : ℝ) (a b : Poly) :
    eval p t u (a * b) = eval p t u a * eval p t u b := by
  classical
  change eval p t u (mul a b) = eval p t u a * eval p t u b
  -- First handle evaluation of the raw term product list.
  have htermMul :
      ∀ (x : Term), ∀ (ys : List Term),
        evalTerms p t u (ys.map (fun y => (Monom.mul x.1 y.1, x.2 * y.2))) =
          evalTerm p t u x * evalTerms p t u ys := by
    intro x ys
    induction ys with
    | nil =>
        simp [evalTerms_nil]
    | cons y ys ih =>
        rcases x with ⟨mx, cx⟩
        rcases y with ⟨my, cy⟩
        -- Unfold the definitions and use multiplicativity of `monomVal`.
        simp [evalTerms_cons, evalTerm, monomVal_mul, ih, mul_add, add_mul, mul_assoc, mul_left_comm, mul_comm]

  have hflat :
      evalTerms p t u
          (List.flatMap
              (fun x => b.terms.map (fun y => (Monom.mul x.1 y.1, x.2 * y.2)))
              a.terms) =
        evalTerms p t u a.terms * evalTerms p t u b.terms := by
    induction a.terms with
    | nil =>
        simp [evalTerms_nil]
    | cons x xs ih =>
        -- Split the flatMap into head/tail, then use the lemma above.
        have ih' :
            evalTerms p t u
                ((List.map
                      (fun x => b.terms.map (fun y => (Monom.mul x.1 y.1, x.2 * y.2)))
                      xs).flatten) =
              evalTerms p t u xs * evalTerms p t u b.terms := by
          simpa [List.flatMap] using ih
        have hx :
            evalTerms p t u (b.terms.map (fun y => (Monom.mul x.1 y.1, x.2 * y.2))) =
              evalTerm p t u x * evalTerms p t u b.terms := by
          simpa using (htermMul x b.terms)
        -- Expand `flatMap` as `flatten (map ...)` and use `evalTerms_append`.
        simp [List.flatMap, List.flatten, evalTerms_append, evalTerms_cons, ih', hx, add_mul, mul_add, add_assoc,
          add_left_comm, add_comm]

  -- `mul` is defined by `mk (flatMap ...)`, and `eval_mk` removes the normalization.
  calc
    eval p t u (mul a b) =
        evalTerms p t u
          (List.flatMap
            (fun x => b.terms.map (fun y => (Monom.mul x.1 y.1, x.2 * y.2)))
            a.terms) := by
          -- Unfold `mul` (which is a `mk`) and apply `eval_mk`.
          simpa [mul] using (eval_mk (p := p) (t := t) (u := u)
            (ts := List.flatMap
              (fun x => b.terms.map (fun y => (Monom.mul x.1 y.1, x.2 * y.2)))
              a.terms))
    _ = evalTerms p t u a.terms * evalTerms p t u b.terms := hflat
    _ = eval p t u a * eval p t u b := by
          rfl

lemma eval_pow (p t u : ℝ) (a : Poly) : ∀ n : Nat,
    eval p t u (a ^ n) = (eval p t u a) ^ n
  | 0 => by
      change eval p t u (pow a 0) = (eval p t u a) ^ 0
      simp [pow, eval_const]
  | n + 1 => by
      change eval p t u (pow a (n + 1)) = (eval p t u a) ^ (n + 1)
      calc
        eval p t u (pow a (n + 1)) = eval p t u (mul (pow a n) a) := by
          simp [pow]
        _ = eval p t u (pow a n) * eval p t u a := by
          -- `mul` is the `(*)` operation on `Poly`.
          simpa using (eval_mul (p := p) (t := t) (u := u) (a := pow a n) (b := a))
        _ = (eval p t u a) ^ n * eval p t u a := by
          have hn : eval p t u (pow a n) = (eval p t u a) ^ n := by
            simpa using (eval_pow (p := p) (t := t) (u := u) (a := a) n)
          simpa [hn]
        _ = (eval p t u a) ^ (n + 1) := by
          simp [pow_succ, mul_assoc]

end

end Poly3

end FiniteDependence.MIS
