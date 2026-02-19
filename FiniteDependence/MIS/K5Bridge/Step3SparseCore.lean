import FiniteDependence.MIS.K5Bridge.Dist7
import FiniteDependence.MIS.K5Bridge.NoDup
import FiniteDependence.MIS.K5Bridge.SparseCertData
import FiniteDependence.MIS.K5Bridge.StepLemmas
import FiniteDependence.MIS.Poly3Eval

namespace FiniteDependence.MIS

namespace K5Bridge

open MeasureTheory Set
open scoped BigOperators ProbabilityTheory

namespace Model

open FiniteDependence.MIS.Model
open K5Data
open FiniteDependence.MIS.Poly3

noncomputable section

namespace Step3

private lemma is01_of_mem_allowedWords {L : Nat} {s : String} (hs : s ∈ K5Data.allowedWords L) :
    Is01String s :=
  Is01String.of_mem_allowedWords (L := L) (s := s) hs

def pPoly : Poly := varP
def tPoly : Poly := varT

def dist7Poly : String → Poly
  | "0010010" => pPoly ^ 2 - tPoly
  | "0010100" => ((-2 : ℚ) • (pPoly ^ 2)) + ((-7 : ℚ) • pPoly) + ((3 : ℚ) • tPoly) + 3
  | "0010101" => (pPoly ^ 2) + ((5 : ℚ) • pPoly) + ((-2 : ℚ) • tPoly) + ((-2 : ℚ) • (1 : Poly))
  | "0100100" => pPoly ^ 2 - tPoly
  | "0100101" => ((-1 : ℚ) • (pPoly ^ 2)) + ((-2 : ℚ) • pPoly) + tPoly + 1
  | "0101001" => ((-1 : ℚ) • (pPoly ^ 2)) + ((-2 : ℚ) • pPoly) + tPoly + 1
  | "0101010" => (pPoly ^ 2) + ((5 : ℚ) • pPoly) + ((-1 : ℚ) • tPoly) + ((-2 : ℚ) • (1 : Poly))
  | "1001001" => pPoly ^ 2 - tPoly
  | "1001010" => ((-1 : ℚ) • (pPoly ^ 2)) + ((-2 : ℚ) • pPoly) + tPoly + 1
  | "1010010" => ((-1 : ℚ) • (pPoly ^ 2)) + ((-2 : ℚ) • pPoly) + tPoly + 1
  | "1010100" => (pPoly ^ 2) + ((5 : ℚ) • pPoly) + ((-2 : ℚ) • tPoly) + ((-2 : ℚ) • (1 : Poly))
  | "1010101" => tPoly
  | _ => 0

def words7 : List String :=
  (K5Data.allowedWords 7).toList

def shortMargPoly (x : String) : Poly :=
  words7.foldl
    (fun acc w => if prefixOf w x.length = x then acc + dist7Poly w else acc)
    0

def rowRhsPoly : RowKind → Poly
  | .norm => 1
  | .stat13 _ => 0
  | .split _ x _ y => shortMargPoly x * shortMargPoly y

def certPoly (cert : List (Nat × ℚ)) : Poly :=
  cert.foldl (fun acc rc => acc + (rc.2 • rowRhsPoly (allRows.getD rc.1 RowKind.norm))) 0

def pVal (μ : Measure FiniteDependence.MIS.State) [IsProbabilityMeasure μ] : ℝ :=
  FiniteDependence.MIS.Model.prob μ (cylStr (a := (0 : ℤ)) "1")

def tVal (μ : Measure FiniteDependence.MIS.State) [IsProbabilityMeasure μ] : ℝ :=
  FiniteDependence.MIS.Model.prob μ (cylStr (a := (0 : ℤ)) "1010101")

private lemma eval_dist7Poly_0010010 (p t : ℝ) :
    Poly3.eval p t 0 (dist7Poly "0010010") = p ^ 2 - t := by
  simp [dist7Poly, pPoly, tPoly, Poly3.eval_sub, Poly3.eval_pow, Poly3.eval_varP, Poly3.eval_varT]

private lemma eval_dist7Poly_0010100 (p t : ℝ) :
    Poly3.eval p t 0 (dist7Poly "0010100") = (-2) * p ^ 2 + (-7) * p + 3 * t + 3 := by
  simp [dist7Poly, pPoly, tPoly, Poly3.eval_add, Poly3.eval_sub, Poly3.eval_smul, Poly3.eval_pow,
    Poly3.eval_varP, Poly3.eval_varT, Poly3.eval_const]

private lemma eval_dist7Poly_0010101 (p t : ℝ) :
    Poly3.eval p t 0 (dist7Poly "0010101") = p ^ 2 + 5 * p - 2 * t - 2 := by
  simp [dist7Poly, pPoly, tPoly, Poly3.eval_add, Poly3.eval_sub, Poly3.eval_smul, Poly3.eval_pow,
    Poly3.eval_varP, Poly3.eval_varT, Poly3.eval_const]
  ring

private lemma eval_dist7Poly_0100100 (p t : ℝ) :
    Poly3.eval p t 0 (dist7Poly "0100100") = p ^ 2 - t := by
  simp [dist7Poly, pPoly, tPoly, Poly3.eval_sub, Poly3.eval_pow, Poly3.eval_varP, Poly3.eval_varT]

private lemma eval_dist7Poly_0100101 (p t : ℝ) :
    Poly3.eval p t 0 (dist7Poly "0100101") = (-1) * p ^ 2 + (-2) * p + t + 1 := by
  simp [dist7Poly, pPoly, tPoly, Poly3.eval_add, Poly3.eval_sub, Poly3.eval_smul, Poly3.eval_pow,
    Poly3.eval_varP, Poly3.eval_varT, Poly3.eval_const]

private lemma eval_dist7Poly_0101001 (p t : ℝ) :
    Poly3.eval p t 0 (dist7Poly "0101001") = (-1) * p ^ 2 + (-2) * p + t + 1 := by
  simp [dist7Poly, pPoly, tPoly, Poly3.eval_add, Poly3.eval_sub, Poly3.eval_smul, Poly3.eval_pow,
    Poly3.eval_varP, Poly3.eval_varT, Poly3.eval_const]

private lemma eval_dist7Poly_0101010 (p t : ℝ) :
    Poly3.eval p t 0 (dist7Poly "0101010") = p ^ 2 + 5 * p - t - 2 := by
  simp [dist7Poly, pPoly, tPoly, Poly3.eval_add, Poly3.eval_sub, Poly3.eval_smul, Poly3.eval_pow,
    Poly3.eval_varP, Poly3.eval_varT, Poly3.eval_const]
  ring

private lemma eval_dist7Poly_1001001 (p t : ℝ) :
    Poly3.eval p t 0 (dist7Poly "1001001") = p ^ 2 - t := by
  simp [dist7Poly, pPoly, tPoly, Poly3.eval_sub, Poly3.eval_pow, Poly3.eval_varP, Poly3.eval_varT]

private lemma eval_dist7Poly_1001010 (p t : ℝ) :
    Poly3.eval p t 0 (dist7Poly "1001010") = (-1) * p ^ 2 + (-2) * p + t + 1 := by
  simp [dist7Poly, pPoly, tPoly, Poly3.eval_add, Poly3.eval_sub, Poly3.eval_smul, Poly3.eval_pow,
    Poly3.eval_varP, Poly3.eval_varT, Poly3.eval_const]

private lemma eval_dist7Poly_1010010 (p t : ℝ) :
    Poly3.eval p t 0 (dist7Poly "1010010") = (-1) * p ^ 2 + (-2) * p + t + 1 := by
  simp [dist7Poly, pPoly, tPoly, Poly3.eval_add, Poly3.eval_sub, Poly3.eval_smul, Poly3.eval_pow,
    Poly3.eval_varP, Poly3.eval_varT, Poly3.eval_const]

private lemma eval_dist7Poly_1010100 (p t : ℝ) :
    Poly3.eval p t 0 (dist7Poly "1010100") = p ^ 2 + 5 * p - 2 * t - 2 := by
  simp [dist7Poly, pPoly, tPoly, Poly3.eval_add, Poly3.eval_sub, Poly3.eval_smul, Poly3.eval_pow,
    Poly3.eval_varP, Poly3.eval_varT, Poly3.eval_const]
  ring

private lemma eval_dist7Poly_1010101 (p t : ℝ) :
    Poly3.eval p t 0 (dist7Poly "1010101") = t := by
  simp [dist7Poly, pPoly, tPoly, Poly3.eval_varT]

private theorem prob_dist7_word_eq_evalPoly (μ : Measure FiniteDependence.MIS.State) [IsProbabilityMeasure μ]
    (hstat : Stationary μ) (hdep : KDependent 5 μ) {w : String} (hw : w ∈ K5Data.allowedWords 7) :
    FiniteDependence.MIS.Model.prob μ (cylStr (a := (0 : ℤ)) w) =
      Poly3.eval (pVal μ) (tVal μ) 0 (dist7Poly w) := by
  have hform := prob_dist7_formulas (μ := μ) hstat hdep
  rcases hform with
    ⟨h0010010, h0010100, h0010101, h0100100, h0100101, h0101001, h0101010, h1001001, h1001010,
      h1010010, h1010100, h1010101⟩
  have hw_cases :
      w = "0010010" ∨ w = "0010100" ∨ w = "0010101" ∨ w = "0100100" ∨ w = "0100101" ∨
        w = "0101001" ∨ w = "0101010" ∨ w = "1001001" ∨ w = "1001010" ∨ w = "1010010" ∨
          w = "1010100" ∨ w = "1010101" := by
    have hWords :
        (K5Data.allowedWords 7).toList =
          ["0010010", "0010100", "0010101", "0100100", "0100101", "0101001",
            "0101010", "1001001", "1001010", "1010010", "1010100", "1010101"] := by
      native_decide
    have hwList : w ∈ (K5Data.allowedWords 7).toList := by
      simpa using hw
    have : w ∈
        ["0010010", "0010100", "0010101", "0100100", "0100101", "0101001",
          "0101010", "1001001", "1001010", "1010010", "1010100", "1010101"] := by
      simpa [hWords] using hwList
    simpa [List.mem_cons, or_assoc, or_left_comm, or_comm] using this
  rcases hw_cases with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · simpa [pVal, tVal] using h0010010.trans (eval_dist7Poly_0010010 (p := pVal μ) (t := tVal μ)).symm
  · simpa [pVal, tVal] using h0010100.trans (eval_dist7Poly_0010100 (p := pVal μ) (t := tVal μ)).symm
  · simpa [pVal, tVal] using h0010101.trans (eval_dist7Poly_0010101 (p := pVal μ) (t := tVal μ)).symm
  · simpa [pVal, tVal] using h0100100.trans (eval_dist7Poly_0100100 (p := pVal μ) (t := tVal μ)).symm
  · simpa [pVal, tVal] using h0100101.trans (eval_dist7Poly_0100101 (p := pVal μ) (t := tVal μ)).symm
  · simpa [pVal, tVal] using h0101001.trans (eval_dist7Poly_0101001 (p := pVal μ) (t := tVal μ)).symm
  · simpa [pVal, tVal] using h0101010.trans (eval_dist7Poly_0101010 (p := pVal μ) (t := tVal μ)).symm
  · simpa [pVal, tVal] using h1001001.trans (eval_dist7Poly_1001001 (p := pVal μ) (t := tVal μ)).symm
  · simpa [pVal, tVal] using h1001010.trans (eval_dist7Poly_1001010 (p := pVal μ) (t := tVal μ)).symm
  · simpa [pVal, tVal] using h1010010.trans (eval_dist7Poly_1010010 (p := pVal μ) (t := tVal μ)).symm
  · simpa [pVal, tVal] using h1010100.trans (eval_dist7Poly_1010100 (p := pVal μ) (t := tVal μ)).symm
  · simpa [pVal, tVal] using h1010101.trans (eval_dist7Poly_1010101 (p := pVal μ) (t := tVal μ)).symm

private def rowLhsProb (μ : Measure FiniteDependence.MIS.State) [IsProbabilityMeasure μ]
    (r : RowKind) : ℝ :=
  ∑ w ∈ allowedWordsFinset 14, (rowCoeff r w : ℝ) * FiniteDependence.MIS.Model.prob μ (cylStr (a := (0 : ℤ)) w)

private lemma sum_prob_allowedWordsFinset_eq_one (μ : Measure FiniteDependence.MIS.State)
    [IsProbabilityMeasure μ] {L : Nat} (hL : 0 < L) :
    (∑ w ∈ allowedWordsFinset L, FiniteDependence.MIS.Model.prob μ (cylStr (a := (0 : ℤ)) w)) = 1 := by
  classical
  have hd :
      PairwiseDisjoint (↑(allowedWordsFinset L) : Set String) (fun w => cylStr (a := (0 : ℤ)) w) :=
    pairwiseDisjoint_cylStr_allowedWords (a := (0 : ℤ)) (L := L)
  have hm : ∀ w ∈ allowedWordsFinset L, MeasurableSet (cylStr (a := (0 : ℤ)) w) := by
    intro w _hw
    simpa using measurableSet_cylStr (a := (0 : ℤ)) (s := w)
  have hprobUnion :
      FiniteDependence.MIS.Model.prob μ (⋃ w ∈ allowedWordsFinset L, cylStr (a := (0 : ℤ)) w) =
        ∑ w ∈ allowedWordsFinset L, FiniteDependence.MIS.Model.prob μ (cylStr (a := (0 : ℤ)) w) :=
    prob_biUnion_finset (μ := μ) (s := allowedWordsFinset L) (f := fun w => cylStr (a := (0 : ℤ)) w) hd hm
  have hunion : (⋃ w ∈ allowedWordsFinset L, cylStr (a := (0 : ℤ)) w) = (univ : Set FiniteDependence.MIS.State) :=
    iUnion_cylStr_allowedWords (a := (0 : ℤ)) (L := L) hL
  calc
    (∑ w ∈ allowedWordsFinset L, FiniteDependence.MIS.Model.prob μ (cylStr (a := (0 : ℤ)) w)) =
        FiniteDependence.MIS.Model.prob μ (⋃ w ∈ allowedWordsFinset L, cylStr (a := (0 : ℤ)) w) := by
          simpa using hprobUnion.symm
    _ = FiniteDependence.MIS.Model.prob μ (univ : Set FiniteDependence.MIS.State) := by
          simp [hunion]
    _ = 1 := FiniteDependence.MIS.Model.prob_univ (μ := μ)

private lemma rowLhsProb_norm_eq_one (μ : Measure FiniteDependence.MIS.State) [IsProbabilityMeasure μ] :
    rowLhsProb μ RowKind.norm = 1 := by
  classical
  calc
    rowLhsProb μ RowKind.norm =
      ∑ w ∈ allowedWordsFinset 14, FiniteDependence.MIS.Model.prob μ (cylStr (a := (0 : ℤ)) w) := by
        simp [rowLhsProb, rowCoeff]
    _ = 1 := sum_prob_allowedWordsFinset_eq_one (μ := μ) (hL := by decide)

private lemma rowLhsProb_stat13_eq_zero (μ : Measure FiniteDependence.MIS.State) [IsProbabilityMeasure μ]
    (hstat : Stationary μ) {u : String} (hu : u ∈ K5Data.allowedWords 13) :
    rowLhsProb μ (.stat13 u) = 0 := by
  have hu01 : Is01String u := is01_of_mem_allowedWords hu
  have huLen : u.length = 13 := length_of_mem_allowedWords (L := 13) (s := u) hu

  have hpref :
      FiniteDependence.MIS.Model.prob μ (cylStr (a := (0 : ℤ)) u) =
        ∑ w ∈ (allowedWordsFinset 14).filter (fun w => prefixOf w 13 = u),
          FiniteDependence.MIS.Model.prob μ (cylStr (a := (0 : ℤ)) w) := by
    simpa using
      (prob_prefix_eq_sum (μ := μ) (a := (0 : ℤ)) (L := 14) (m := 13) (hL := by decide)
        (hm := by decide) (x := u) hu01 huLen)

  have hsuf :
      FiniteDependence.MIS.Model.prob μ (cylStr (a := (0 : ℤ) + 1) u) =
        ∑ w ∈ (allowedWordsFinset (13 + 1)).filter (fun w => suffix1 w = u),
          FiniteDependence.MIS.Model.prob μ (cylStr (a := (0 : ℤ)) w) := by
    simpa using
      (prob_suffix1_eq_sum (μ := μ) (a := (0 : ℤ)) (m := 13) (x := u) hu01 huLen)

  have hsuf' :
      FiniteDependence.MIS.Model.prob μ (cylStr (a := (0 : ℤ) + 1) u) =
        ∑ w ∈ (allowedWordsFinset 14).filter (fun w => suffixFrom w 1 = u),
          FiniteDependence.MIS.Model.prob μ (cylStr (a := (0 : ℤ)) w) := by
    simpa [suffix1, suffixFrom, Nat.add_comm] using hsuf

  have hshift :
      FiniteDependence.MIS.Model.prob μ (cylStr (a := (0 : ℤ) + 1) u) =
        FiniteDependence.MIS.Model.prob μ (cylStr (a := (0 : ℤ)) u) := by
    simpa using (Stationary.prob_cylStr_add_nat (μ := μ) hstat (a := (0 : ℤ)) (n := 1) (s := u))

  have hsum_eq :
      (∑ w ∈ (allowedWordsFinset 14).filter (fun w => prefixOf w 13 = u),
          FiniteDependence.MIS.Model.prob μ (cylStr (a := (0 : ℤ)) w)) =
        (∑ w ∈ (allowedWordsFinset 14).filter (fun w => suffix1 w = u),
          FiniteDependence.MIS.Model.prob μ (cylStr (a := (0 : ℤ)) w)) := by
    calc
      (∑ w ∈ (allowedWordsFinset 14).filter (fun w => prefixOf w 13 = u),
            FiniteDependence.MIS.Model.prob μ (cylStr (a := (0 : ℤ)) w))
          = FiniteDependence.MIS.Model.prob μ (cylStr (a := (0 : ℤ)) u) := by
              simpa using hpref.symm
      _ = FiniteDependence.MIS.Model.prob μ (cylStr (a := (0 : ℤ) + 1) u) := by
              simpa using hshift.symm
      _ = (∑ w ∈ (allowedWordsFinset 14).filter (fun w => suffix1 w = u),
            FiniteDependence.MIS.Model.prob μ (cylStr (a := (0 : ℤ)) w)) := by
              simpa [suffix1, suffixFrom] using hsuf'

  have hA :
      (∑ w ∈ allowedWordsFinset 14,
          (if prefixOf w 13 = u then (1 : ℝ) else 0) *
            FiniteDependence.MIS.Model.prob μ (cylStr (a := (0 : ℤ)) w)) =
        (∑ w ∈ (allowedWordsFinset 14).filter (fun w => prefixOf w 13 = u),
          FiniteDependence.MIS.Model.prob μ (cylStr (a := (0 : ℤ)) w)) := by
    calc
      (∑ w ∈ allowedWordsFinset 14,
          (if prefixOf w 13 = u then (1 : ℝ) else 0) *
            FiniteDependence.MIS.Model.prob μ (cylStr (a := (0 : ℤ)) w)) =
        (∑ w ∈ allowedWordsFinset 14,
          if prefixOf w 13 = u then FiniteDependence.MIS.Model.prob μ (cylStr (a := (0 : ℤ)) w) else 0) := by
          simp
      _ = (∑ w ∈ (allowedWordsFinset 14).filter (fun w => prefixOf w 13 = u),
            FiniteDependence.MIS.Model.prob μ (cylStr (a := (0 : ℤ)) w)) := by
          simpa [Finset.sum_filter]

  have hB :
      (∑ w ∈ allowedWordsFinset 14,
          (if suffixFrom w 1 = u then (1 : ℝ) else 0) *
            FiniteDependence.MIS.Model.prob μ (cylStr (a := (0 : ℤ)) w)) =
        (∑ w ∈ (allowedWordsFinset 14).filter (fun w => suffixFrom w 1 = u),
          FiniteDependence.MIS.Model.prob μ (cylStr (a := (0 : ℤ)) w)) := by
    calc
      (∑ w ∈ allowedWordsFinset 14,
          (if suffixFrom w 1 = u then (1 : ℝ) else 0) *
            FiniteDependence.MIS.Model.prob μ (cylStr (a := (0 : ℤ)) w)) =
        (∑ w ∈ allowedWordsFinset 14,
          if suffixFrom w 1 = u then FiniteDependence.MIS.Model.prob μ (cylStr (a := (0 : ℤ)) w) else 0) := by
          simp
      _ = (∑ w ∈ (allowedWordsFinset 14).filter (fun w => suffixFrom w 1 = u),
            FiniteDependence.MIS.Model.prob μ (cylStr (a := (0 : ℤ)) w)) := by
          simpa [Finset.sum_filter]

  have hA' :
      (∑ w ∈ allowedWordsFinset 14,
          if prefixOf w 13 = u then FiniteDependence.MIS.Model.prob μ (cylStr (a := (0 : ℤ)) w) else 0) =
        (∑ w ∈ (allowedWordsFinset 14).filter (fun w => prefixOf w 13 = u),
          FiniteDependence.MIS.Model.prob μ (cylStr (a := (0 : ℤ)) w)) := by
    simpa [Finset.sum_filter]

  have hB' :
      (∑ w ∈ allowedWordsFinset 14,
          if suffixFrom w 1 = u then FiniteDependence.MIS.Model.prob μ (cylStr (a := (0 : ℤ)) w) else 0) =
        (∑ w ∈ (allowedWordsFinset 14).filter (fun w => suffixFrom w 1 = u),
          FiniteDependence.MIS.Model.prob μ (cylStr (a := (0 : ℤ)) w)) := by
    simpa [Finset.sum_filter]

  have hRowExpand :
      rowLhsProb μ (.stat13 u) =
        (∑ w ∈ allowedWordsFinset 14,
            (↑(if prefixOf w 13 = u then (1 : ℚ) else 0) : ℝ) *
              FiniteDependence.MIS.Model.prob μ (cylStr (a := (0 : ℤ)) w)) -
          (∑ w ∈ allowedWordsFinset 14,
            (↑(if suffixFrom w 1 = u then (1 : ℚ) else 0) : ℝ) *
              FiniteDependence.MIS.Model.prob μ (cylStr (a := (0 : ℤ)) w)) := by
    simp [rowLhsProb, rowCoeff, sub_mul, Finset.sum_sub_distrib]

  have hPrefCast :
      (∑ w ∈ allowedWordsFinset 14,
          (↑(if prefixOf w 13 = u then (1 : ℚ) else 0) : ℝ) *
            FiniteDependence.MIS.Model.prob μ (cylStr (a := (0 : ℤ)) w)) =
        (∑ w ∈ allowedWordsFinset 14,
          if prefixOf w 13 = u then FiniteDependence.MIS.Model.prob μ (cylStr (a := (0 : ℤ)) w) else 0) := by
    refine Finset.sum_congr rfl ?_
    intro w hw
    by_cases hcond : prefixOf w 13 = u
    · simp [hcond]
    · simp [hcond]

  have hSufCast :
      (∑ w ∈ allowedWordsFinset 14,
          (↑(if suffixFrom w 1 = u then (1 : ℚ) else 0) : ℝ) *
            FiniteDependence.MIS.Model.prob μ (cylStr (a := (0 : ℤ)) w)) =
        (∑ w ∈ allowedWordsFinset 14,
          if suffixFrom w 1 = u then FiniteDependence.MIS.Model.prob μ (cylStr (a := (0 : ℤ)) w) else 0) := by
    refine Finset.sum_congr rfl ?_
    intro w hw
    by_cases hcond : suffixFrom w 1 = u
    · simp [hcond]
    · simp [hcond]

  calc
    rowLhsProb μ (.stat13 u) =
      (∑ w ∈ allowedWordsFinset 14,
          (↑(if prefixOf w 13 = u then (1 : ℚ) else 0) : ℝ) *
            FiniteDependence.MIS.Model.prob μ (cylStr (a := (0 : ℤ)) w)) -
        (∑ w ∈ allowedWordsFinset 14,
          (↑(if suffixFrom w 1 = u then (1 : ℚ) else 0) : ℝ) *
            FiniteDependence.MIS.Model.prob μ (cylStr (a := (0 : ℤ)) w)) := hRowExpand
    _ = (∑ w ∈ allowedWordsFinset 14,
          if prefixOf w 13 = u then FiniteDependence.MIS.Model.prob μ (cylStr (a := (0 : ℤ)) w) else 0) -
        (∑ w ∈ allowedWordsFinset 14,
          if suffixFrom w 1 = u then FiniteDependence.MIS.Model.prob μ (cylStr (a := (0 : ℤ)) w) else 0) := by
          simpa [hPrefCast, hSufCast]
    _ = (∑ w ∈ (allowedWordsFinset 14).filter (fun w => prefixOf w 13 = u),
          FiniteDependence.MIS.Model.prob μ (cylStr (a := (0 : ℤ)) w)) -
        (∑ w ∈ (allowedWordsFinset 14).filter (fun w => suffixFrom w 1 = u),
          FiniteDependence.MIS.Model.prob μ (cylStr (a := (0 : ℤ)) w)) := by
          rw [hA', hB']
    _ = 0 := by linarith [hsum_eq]

private lemma rowLhsProb_split_eq_prod (μ : Measure FiniteDependence.MIS.State) [IsProbabilityMeasure μ]
    (hstat : Stationary μ) (hdep : KDependent 5 μ)
    {m n : Nat} {x y : String}
    (hx : x ∈ K5Data.allowedWords m) (hy : y ∈ K5Data.allowedWords n)
    (hlen : m + 5 + n = 14) :
    rowLhsProb μ (.split m x n y) =
      FiniteDependence.MIS.Model.prob μ (cylStr (a := (0 : ℤ)) x) *
        FiniteDependence.MIS.Model.prob μ (cylStr (a := (0 : ℤ)) y) := by
  have hx01 : Is01String x := is01_of_mem_allowedWords hx
  have hy01 : Is01String y := is01_of_mem_allowedWords hy
  have hxLen : x.length = m := length_of_mem_allowedWords (L := m) (s := x) hx
  have hyLen : y.length = n := length_of_mem_allowedWords (L := n) (s := y) hy
  have hprod := prob_prod_gap5 (μ := μ) hstat hdep (m := m) (n := n) (x := x) (y := y) hx01 hy01 hxLen hyLen
  have hsum :
      FiniteDependence.MIS.Model.prob μ (cylStr (a := (0 : ℤ)) x) *
          FiniteDependence.MIS.Model.prob μ (cylStr (a := (0 : ℤ)) y) =
        ∑ w ∈ (allowedWordsFinset 14).filter (fun w => prefixOf w m = x ∧ suffixFrom w (m + 5) = y),
          FiniteDependence.MIS.Model.prob μ (cylStr (a := (0 : ℤ)) w) := by
    simpa [hlen] using hprod

  have hA :
      rowLhsProb μ (.split m x n y) =
        (∑ w ∈ (allowedWordsFinset 14).filter (fun w => prefixOf w m = x ∧ suffixFrom w (m + 5) = y),
          FiniteDependence.MIS.Model.prob μ (cylStr (a := (0 : ℤ)) w)) := by
    calc
      rowLhsProb μ (.split m x n y) =
        (∑ w ∈ allowedWordsFinset 14,
            (↑(if prefixOf w m = x ∧ suffixFrom w (m + 5) = y then (1 : ℚ) else 0) : ℝ) *
              FiniteDependence.MIS.Model.prob μ (cylStr (a := (0 : ℤ)) w)) := by
            simp [rowLhsProb, rowCoeff]
      _ = (∑ w ∈ allowedWordsFinset 14,
            if prefixOf w m = x ∧ suffixFrom w (m + 5) = y
              then FiniteDependence.MIS.Model.prob μ (cylStr (a := (0 : ℤ)) w) else 0) := by
            have hCast :
                (∑ w ∈ allowedWordsFinset 14,
                    (↑(if prefixOf w m = x ∧ suffixFrom w (m + 5) = y then (1 : ℚ) else 0) : ℝ) *
                      FiniteDependence.MIS.Model.prob μ (cylStr (a := (0 : ℤ)) w)) =
                  (∑ w ∈ allowedWordsFinset 14,
                    if prefixOf w m = x ∧ suffixFrom w (m + 5) = y
                      then FiniteDependence.MIS.Model.prob μ (cylStr (a := (0 : ℤ)) w) else 0) := by
                  refine Finset.sum_congr rfl ?_
                  intro w hw
                  by_cases hcond : prefixOf w m = x ∧ suffixFrom w (m + 5) = y
                  · simp [hcond]
                  · simp [hcond]
            simpa [hCast]
      _ = (∑ w ∈ (allowedWordsFinset 14).filter (fun w => prefixOf w m = x ∧ suffixFrom w (m + 5) = y),
            FiniteDependence.MIS.Model.prob μ (cylStr (a := (0 : ℤ)) w)) := by
            simpa [Finset.sum_filter]

  linarith [hA, hsum]

private lemma foldl_if_add_eq_map_sum (l : List String) (f : String → ℝ) (p : String → Bool) :
    l.foldl (fun acc w => if p w then acc + f w else acc) 0 = ((l.filter p).map f).sum := by
  have haux :
      ∀ init : ℝ,
        l.foldl (fun acc w => if p w then acc + f w else acc) init =
          init + ((l.filter p).map f).sum := by
    induction l with
    | nil =>
        intro init
        simp
    | cons w ws ih =>
        intro init
        by_cases hw : p w
        · simp [List.foldl, hw, ih, add_assoc, add_left_comm, add_comm]
        · simp [List.foldl, hw, ih, add_assoc, add_left_comm, add_comm]
  simpa using haux 0

private lemma eval_foldl_shortMarg (p t : ℝ) (x : String) :
    ∀ (l : List String) (acc : Poly),
      Poly3.eval p t 0
          (l.foldl (fun a w => if prefixOf w x.length = x then a + dist7Poly w else a) acc) =
        l.foldl
          (fun b w => if prefixOf w x.length = x then b + Poly3.eval p t 0 (dist7Poly w) else b)
          (Poly3.eval p t 0 acc)
  | [], acc => by simp
  | w :: ws, acc => by
      by_cases hw : prefixOf w x.length = x
      · simp [List.foldl, hw, Poly3.eval_add, eval_foldl_shortMarg (p := p) (t := t) (x := x) ws (acc + dist7Poly w)]
      · simp [List.foldl, hw, eval_foldl_shortMarg (p := p) (t := t) (x := x) ws acc]

private theorem prob_short_eq_eval_shortMargPoly (μ : Measure FiniteDependence.MIS.State) [IsProbabilityMeasure μ]
    (hstat : Stationary μ) (hdep : KDependent 5 μ)
    {m : Nat} {x : String} (hx : x ∈ K5Data.allowedWords m) (hm : m ≤ 7) :
    FiniteDependence.MIS.Model.prob μ (cylStr (a := (0 : ℤ)) x) =
      Poly3.eval (pVal μ) (tVal μ) 0 (shortMargPoly x) := by
  have hx01 : Is01String x := is01_of_mem_allowedWords hx
  have hxLen : x.length = m := length_of_mem_allowedWords (L := m) (s := x) hx
  have hpref :
      FiniteDependence.MIS.Model.prob μ (cylStr (a := (0 : ℤ)) x) =
        ∑ w ∈ (allowedWordsFinset 7).filter (fun w => prefixOf w m = x),
          FiniteDependence.MIS.Model.prob μ (cylStr (a := (0 : ℤ)) w) := by
    simpa using
      (prob_prefix_eq_sum (μ := μ) (a := (0 : ℤ)) (L := 7) (m := m) (hL := by decide)
        (hm := hm) (x := x) hx01 hxLen)

  have hsum_eval :
      (∑ w ∈ (allowedWordsFinset 7).filter (fun w => prefixOf w m = x),
          FiniteDependence.MIS.Model.prob μ (cylStr (a := (0 : ℤ)) w)) =
        (∑ w ∈ (allowedWordsFinset 7).filter (fun w => prefixOf w m = x),
          Poly3.eval (pVal μ) (tVal μ) 0 (dist7Poly w)) := by
    refine Finset.sum_congr rfl ?_
    intro w hw
    have hw0 : w ∈ allowedWordsFinset 7 := Finset.mem_of_mem_filter w hw
    have hw7 : w ∈ K5Data.allowedWords 7 := (mem_allowedWordsFinset_iff (L := 7) (s := w)).1 hw0
    simpa using (prob_dist7_word_eq_evalPoly (μ := μ) hstat hdep hw7)

  have hWordsNodup : words7.Nodup := by
    simpa [words7] using (allowedWords_nodup 7)

  let pred : String → Bool := fun w => prefixOf w x.length = x
  let fval : String → ℝ := fun w => Poly3.eval (pVal μ) (tVal μ) 0 (dist7Poly w)

  have hFoldEval :
      Poly3.eval (pVal μ) (tVal μ) 0 (shortMargPoly x) =
        words7.foldl (fun acc w => if pred w then acc + fval w else acc) 0 := by
    have h := eval_foldl_shortMarg (p := pVal μ) (t := tVal μ) (x := x) words7 (0 : Poly)
    simpa [shortMargPoly, pred, fval, Poly3.eval_const] using h

  have hFoldList :
      words7.foldl (fun acc w => if pred w then acc + fval w else acc) 0 =
        ((words7.filter pred).map fval).sum := by
    simpa [pred, fval] using foldl_if_add_eq_map_sum (l := words7) (f := fval) (p := pred)

  have hListToFinset :
      ((words7.filter pred).map fval).sum =
        ∑ w ∈ (words7.filter pred).toFinset, fval w := by
    have hNodupFilter : (words7.filter pred).Nodup := hWordsNodup.filter pred
    simpa using (List.sum_toFinset fval hNodupFilter).symm

  have hFilterToFinset :
      (words7.filter pred).toFinset = words7.toFinset.filter (pred ·) := by
    simpa using (List.toFinset_filter (s := words7) (p := pred))

  have hWordsFinset : words7.toFinset = allowedWordsFinset 7 := by
    simp [words7, allowedWordsFinset]

  have hFinset :
      (∑ w ∈ (allowedWordsFinset 7).filter (fun w => prefixOf w m = x), fval w) =
        ∑ w ∈ (allowedWordsFinset 7).filter (pred ·), fval w := by
    simp [pred, hxLen]

  calc
    FiniteDependence.MIS.Model.prob μ (cylStr (a := (0 : ℤ)) x) =
      (∑ w ∈ (allowedWordsFinset 7).filter (fun w => prefixOf w m = x),
        FiniteDependence.MIS.Model.prob μ (cylStr (a := (0 : ℤ)) w)) := hpref
    _ = (∑ w ∈ (allowedWordsFinset 7).filter (fun w => prefixOf w m = x),
          fval w) := by simpa [fval] using hsum_eval
    _ = (∑ w ∈ (allowedWordsFinset 7).filter (pred ·), fval w) := hFinset
    _ = (∑ w ∈ (words7.filter pred).toFinset, fval w) := by
          simpa [hFilterToFinset, hWordsFinset]
    _ = ((words7.filter pred).map fval).sum := by
          simpa [hListToFinset] using hListToFinset.symm
    _ = words7.foldl (fun acc w => if pred w then acc + fval w else acc) 0 := by
          simpa [hFoldList] using hFoldList.symm
    _ = Poly3.eval (pVal μ) (tVal μ) 0 (shortMargPoly x) := by
          simpa [hFoldEval] using hFoldEval.symm

def rowValidB : RowKind → Bool
  | .norm => true
  | .stat13 u => decide (u ∈ K5Data.allowedWords 13)
  | .split m x n y =>
      decide (x ∈ K5Data.allowedWords m ∧ y ∈ K5Data.allowedWords n ∧ m + 5 + n = 14 ∧ m ≤ 7 ∧ n ≤ 7)

theorem allRows_rowValidB :
    allRows.all rowValidB = true := by
  native_decide

private lemma allRows_rowValidB_forall :
    ∀ r ∈ allRows, rowValidB r = true := by
  have hAll :
      allRows.all (fun r => decide (rowValidB r = true)) = true := by
    simpa [Bool.decide_eq_true] using allRows_rowValidB
  exact
    (List.all_iff_forall_prop (l := allRows) (p := fun r => rowValidB r = true)).1 (by
      simpa using hAll)

private lemma rowValidB_getD_true (i : Nat) :
    rowValidB (allRows.getD i RowKind.norm) = true := by
  have hconv : allRows.getD i RowKind.norm = allRows[i]?.getD RowKind.norm := by
    simpa using (List.getD_eq_getElem?_getD (l := allRows) (n := i) (d := RowKind.norm))
  have hmain : rowValidB (allRows[i]?.getD RowKind.norm) = true := by
    by_cases hi : i < allRows.length
    · have hmem : allRows[i] ∈ allRows := by
        simpa using (List.get_mem allRows ⟨i, hi⟩)
      have hvalid : rowValidB allRows[i] = true := allRows_rowValidB_forall (allRows[i]) hmem
      have hsome : allRows[i]? = some allRows[i] := by
        simpa [List.getElem?_eq_some_iff] using hi
      simpa [hsome] using hvalid
    · have hnone : allRows[i]? = none := by
        exact List.getElem?_eq_none (Nat.le_of_not_gt hi)
      simpa [hnone, rowValidB]
  simpa [hconv] using hmain

private lemma rowLhsProb_eq_eval_rowRhsPoly_of_valid (μ : Measure FiniteDependence.MIS.State)
    [IsProbabilityMeasure μ] (hstat : Stationary μ) (hdep : KDependent 5 μ)
    (r : RowKind) (hrValid : rowValidB r = true) :
    rowLhsProb μ r = Poly3.eval (pVal μ) (tVal μ) 0 (rowRhsPoly r) := by
  cases r with
  | norm =>
      simpa [rowRhsPoly, Poly3.eval_const] using rowLhsProb_norm_eq_one (μ := μ)
  | stat13 u =>
      have hu : u ∈ K5Data.allowedWords 13 := by
        simpa [rowValidB] using hrValid
      have hrow : rowLhsProb μ (.stat13 u) = 0 :=
        rowLhsProb_stat13_eq_zero (μ := μ) hstat hu
      simpa [rowRhsPoly, Poly3.eval_const] using hrow
  | split m x n y =>
      have hsplitData :
          x ∈ K5Data.allowedWords m ∧ y ∈ K5Data.allowedWords n ∧
            m + 5 + n = 14 ∧ m ≤ 7 ∧ n ≤ 7 := by
        simpa [rowValidB] using hrValid
      rcases hsplitData with ⟨hx, hy, hlen, hm, hn⟩
      have hrow :
          rowLhsProb μ (.split m x n y) =
            FiniteDependence.MIS.Model.prob μ (cylStr (a := (0 : ℤ)) x) *
              FiniteDependence.MIS.Model.prob μ (cylStr (a := (0 : ℤ)) y) :=
        rowLhsProb_split_eq_prod (μ := μ) hstat hdep hx hy hlen
      have hxEval :
          FiniteDependence.MIS.Model.prob μ (cylStr (a := (0 : ℤ)) x) =
            Poly3.eval (pVal μ) (tVal μ) 0 (shortMargPoly x) :=
        prob_short_eq_eval_shortMargPoly (μ := μ) hstat hdep hx hm
      have hyEval :
          FiniteDependence.MIS.Model.prob μ (cylStr (a := (0 : ℤ)) y) =
            Poly3.eval (pVal μ) (tVal μ) 0 (shortMargPoly y) :=
        prob_short_eq_eval_shortMargPoly (μ := μ) hstat hdep hy hn
      calc
        rowLhsProb μ (.split m x n y) =
          FiniteDependence.MIS.Model.prob μ (cylStr (a := (0 : ℤ)) x) *
            FiniteDependence.MIS.Model.prob μ (cylStr (a := (0 : ℤ)) y) := hrow
        _ =
          Poly3.eval (pVal μ) (tVal μ) 0 (shortMargPoly x) *
            Poly3.eval (pVal μ) (tVal μ) 0 (shortMargPoly y) := by
              rw [hxEval, hyEval]
        _ = Poly3.eval (pVal μ) (tVal μ) 0 (shortMargPoly x * shortMargPoly y) := by
              simp [Poly3.eval_mul]
        _ = Poly3.eval (pVal μ) (tVal μ) 0 (rowRhsPoly (.split m x n y)) := by
              simp [rowRhsPoly]

private lemma rowLhsProb_eq_eval_rowRhsPoly_getD (μ : Measure FiniteDependence.MIS.State)
    [IsProbabilityMeasure μ] (hstat : Stationary μ) (hdep : KDependent 5 μ) (i : Nat) :
    rowLhsProb μ (allRows.getD i RowKind.norm) =
      Poly3.eval (pVal μ) (tVal μ) 0 (rowRhsPoly (allRows.getD i RowKind.norm)) := by
  exact rowLhsProb_eq_eval_rowRhsPoly_of_valid (μ := μ) hstat hdep
    (allRows.getD i RowKind.norm) (rowValidB_getD_true i)

private def certLhsProb (μ : Measure FiniteDependence.MIS.State) [IsProbabilityMeasure μ]
    (cert : List (Nat × ℚ)) : ℝ :=
  cert.foldl
    (fun acc rc => acc + (rc.2 : ℝ) * rowLhsProb μ (allRows.getD rc.1 RowKind.norm))
    0

private def coeffFnStep (cf : String → ℚ) (rc : Nat × ℚ) : String → ℚ :=
  fun w => cf w + rc.2 * rowCoeff (allRows.getD rc.1 RowKind.norm) w

private def coeffFnFromCert (cert : List (Nat × ℚ)) : String → ℚ :=
  cert.foldl coeffFnStep (fun _ => 0)

private lemma coeffFn_fold_apply_eq_fold (cert : List (Nat × ℚ))
    (cf : String → ℚ) (w : String) :
    (cert.foldl coeffFnStep cf) w =
      cert.foldl
        (fun acc rc => acc + rc.2 * rowCoeff (allRows.getD rc.1 RowKind.norm) w)
        (cf w) := by
  induction cert generalizing cf with
  | nil =>
      simp [coeffFnStep]
  | cons rc cs ih =>
      simp [List.foldl, coeffFnStep, ih]

private lemma coeffFnFromCert_eq_certCoeffAt (cert : List (Nat × ℚ)) (w : String) :
    coeffFnFromCert cert w = certCoeffAt cert w := by
  simpa [coeffFnFromCert, certCoeffAt] using
    (coeffFn_fold_apply_eq_fold (cert := cert) (cf := fun _ => 0) (w := w))

private lemma certFold_sum (μ : Measure FiniteDependence.MIS.State) [IsProbabilityMeasure μ] :
    ∀ (cert : List (Nat × ℚ)) (cf : String → ℚ),
      cert.foldl
          (fun acc rc => acc + (rc.2 : ℝ) * rowLhsProb μ (allRows.getD rc.1 RowKind.norm))
          (∑ w ∈ allowedWordsFinset 14, (cf w : ℝ) * FiniteDependence.MIS.Model.prob μ (cylStr (a := (0 : ℤ)) w))
      =
        ∑ w ∈ allowedWordsFinset 14, ((cert.foldl coeffFnStep cf) w : ℝ) *
          FiniteDependence.MIS.Model.prob μ (cylStr (a := (0 : ℤ)) w)
  | [], cf => by
      simp
  | rc :: cs, cf => by
      let f : ℝ → (Nat × ℚ) → ℝ :=
        fun acc rq => acc + (rq.2 : ℝ) * rowLhsProb μ (allRows.getD rq.1 RowKind.norm)
      let init : ℝ :=
        ∑ w ∈ allowedWordsFinset 14, (cf w : ℝ) * FiniteDependence.MIS.Model.prob μ (cylStr (a := (0 : ℤ)) w)
      let init' : ℝ :=
        ∑ w ∈ allowedWordsFinset 14, ((coeffFnStep cf rc) w : ℝ) *
          FiniteDependence.MIS.Model.prob μ (cylStr (a := (0 : ℤ)) w)
      let r : RowKind := allRows.getD rc.1 RowKind.norm
      have hRowEval :
          rowLhsProb μ r =
            ∑ w ∈ allowedWordsFinset 14,
              (rowCoeff r w : ℝ) * FiniteDependence.MIS.Model.prob μ (cylStr (a := (0 : ℤ)) w) := by
        rfl
      have hSumStep : init + (rc.2 : ℝ) * rowLhsProb μ r = init' := by
        calc
          init + (rc.2 : ℝ) * rowLhsProb μ r
              = init + (rc.2 : ℝ) *
                  (∑ w ∈ allowedWordsFinset 14,
                    (rowCoeff r w : ℝ) * FiniteDependence.MIS.Model.prob μ (cylStr (a := (0 : ℤ)) w)) := by
                  simp [hRowEval]
          _ =
              (∑ w ∈ allowedWordsFinset 14, (cf w : ℝ) * FiniteDependence.MIS.Model.prob μ (cylStr (a := (0 : ℤ)) w)) +
                (∑ w ∈ allowedWordsFinset 14,
                  ((rc.2 : ℝ) * (rowCoeff r w : ℝ)) *
                    FiniteDependence.MIS.Model.prob μ (cylStr (a := (0 : ℤ)) w)) := by
                  unfold init
                  refine congrArg (fun z => (∑ w ∈ allowedWordsFinset 14,
                    (cf w : ℝ) * FiniteDependence.MIS.Model.prob μ (cylStr (a := (0 : ℤ)) w)) + z) ?_
                  simp [Finset.mul_sum, mul_assoc, mul_left_comm, mul_comm]
          _ =
              ∑ w ∈ allowedWordsFinset 14,
                ((cf w : ℝ) * FiniteDependence.MIS.Model.prob μ (cylStr (a := (0 : ℤ)) w) +
                  ((rc.2 : ℝ) * (rowCoeff r w : ℝ)) *
                    FiniteDependence.MIS.Model.prob μ (cylStr (a := (0 : ℤ)) w)) := by
                  simp [Finset.sum_add_distrib]
          _ =
              ∑ w ∈ allowedWordsFinset 14,
                (((cf w : ℝ) + (rc.2 : ℝ) * (rowCoeff r w : ℝ)) *
                  FiniteDependence.MIS.Model.prob μ (cylStr (a := (0 : ℤ)) w)) := by
                  refine Finset.sum_congr rfl ?_
                  intro w hw
                  ring
          _ = init' := by
              simp [init', coeffFnStep, r]
      have hInit : f init rc = init' := by
        simpa [f, init, r] using hSumStep
      change (rc :: cs).foldl f init =
        ∑ w ∈ allowedWordsFinset 14, (((rc :: cs).foldl coeffFnStep cf) w : ℝ) *
          FiniteDependence.MIS.Model.prob μ (cylStr (a := (0 : ℤ)) w)
      calc
        (rc :: cs).foldl f init = cs.foldl f (f init rc) := by simp
        _ = cs.foldl f init' := by simpa [hInit]
        _ =
            ∑ w ∈ allowedWordsFinset 14, ((cs.foldl coeffFnStep (coeffFnStep cf rc)) w : ℝ) *
              FiniteDependence.MIS.Model.prob μ (cylStr (a := (0 : ℤ)) w) := by
            simpa [f, init'] using certFold_sum (μ := μ) cs (coeffFnStep cf rc)
        _ =
            ∑ w ∈ allowedWordsFinset 14, (((rc :: cs).foldl coeffFnStep cf) w : ℝ) *
              FiniteDependence.MIS.Model.prob μ (cylStr (a := (0 : ℤ)) w) := by
            simp [List.foldl]

private theorem certLhsProb_eq_sum_certCoeffAt (μ : Measure FiniteDependence.MIS.State)
    [IsProbabilityMeasure μ]
    (cert : List (Nat × ℚ)) :
    certLhsProb μ cert =
      ∑ w ∈ allowedWordsFinset 14, (certCoeffAt cert w : ℝ) *
        FiniteDependence.MIS.Model.prob μ (cylStr (a := (0 : ℤ)) w) := by
  have hFold := certFold_sum (μ := μ) cert (fun _ => 0)
  have hCoeff :
      (cert.foldl coeffFnStep (fun _ => 0)) = coeffFnFromCert cert := rfl
  calc
    certLhsProb μ cert =
      cert.foldl
        (fun acc rc => acc + (rc.2 : ℝ) * rowLhsProb μ (allRows.getD rc.1 RowKind.norm)) 0 := by
          rfl
    _ =
      cert.foldl
        (fun acc rc => acc + (rc.2 : ℝ) * rowLhsProb μ (allRows.getD rc.1 RowKind.norm))
        (∑ w ∈ allowedWordsFinset 14, ((0 : ℚ) : ℝ) *
          FiniteDependence.MIS.Model.prob μ (cylStr (a := (0 : ℤ)) w)) := by
          simp
    _ =
      ∑ w ∈ allowedWordsFinset 14, ((cert.foldl coeffFnStep (fun _ => 0)) w : ℝ) *
        FiniteDependence.MIS.Model.prob μ (cylStr (a := (0 : ℤ)) w) := by
          simpa using hFold
    _ =
      ∑ w ∈ allowedWordsFinset 14, (coeffFnFromCert cert w : ℝ) *
        FiniteDependence.MIS.Model.prob μ (cylStr (a := (0 : ℤ)) w) := by
          simp [hCoeff]
    _ =
      ∑ w ∈ allowedWordsFinset 14, (certCoeffAt cert w : ℝ) *
        FiniteDependence.MIS.Model.prob μ (cylStr (a := (0 : ℤ)) w) := by
          refine Finset.sum_congr rfl ?_
          intro w hw
          simp [coeffFnFromCert_eq_certCoeffAt]

private theorem certLhsProb_eq_eval_certPoly (μ : Measure FiniteDependence.MIS.State)
    [IsProbabilityMeasure μ] (hstat : Stationary μ) (hdep : KDependent 5 μ)
    (cert : List (Nat × ℚ)) :
    certLhsProb μ cert = Poly3.eval (pVal μ) (tVal μ) 0 (certPoly cert) := by
  let fL : ℝ → (Nat × ℚ) → ℝ :=
    fun acc rc => acc + (rc.2 : ℝ) * rowLhsProb μ (allRows.getD rc.1 RowKind.norm)
  let fR : ℝ → (Nat × ℚ) → ℝ :=
    fun acc rc =>
      acc + (rc.2 : ℝ) * Poly3.eval (pVal μ) (tVal μ) 0 (rowRhsPoly (allRows.getD rc.1 RowKind.norm))
  have hRows : cert.foldl fL 0 = cert.foldl fR 0 := by
    have hAux : ∀ (cs : List (Nat × ℚ)) (init : ℝ), cs.foldl fL init = cs.foldl fR init := by
      intro cs
      induction cs with
      | nil =>
          intro init
          simp [fL, fR]
      | cons rc cs ih =>
          intro init
          have hRow := rowLhsProb_eq_eval_rowRhsPoly_getD (μ := μ) hstat hdep rc.1
          have hRow' :
              rowLhsProb μ (allRows[rc.1]?.getD RowKind.norm) =
                Poly3.eval (pVal μ) (tVal μ) 0 (rowRhsPoly (allRows[rc.1]?.getD RowKind.norm)) := by
            simpa [List.getD_eq_getElem?_getD] using hRow
          have hstep :
              fL init rc = fR init rc := by
            simpa [fL, fR] using congrArg (fun z => init + (rc.2 : ℝ) * z) hRow'
          calc
            (rc :: cs).foldl fL init = cs.foldl fL (fL init rc) := by simp [List.foldl]
            _ = cs.foldl fL (fR init rc) := by simpa [hstep]
            _ = cs.foldl fR (fR init rc) := ih (fR init rc)
            _ = (rc :: cs).foldl fR init := by simp [List.foldl]
    exact hAux cert 0
  have hEval :
      cert.foldl fR 0 = Poly3.eval (pVal μ) (tVal μ) 0 (certPoly cert) := by
    have hAux :
        ∀ (cs : List (Nat × ℚ)) (accR : ℝ) (accP : Poly),
          accR = Poly3.eval (pVal μ) (tVal μ) 0 accP →
            cs.foldl fR accR =
              Poly3.eval (pVal μ) (tVal μ) 0
                (cs.foldl
                  (fun acc rc => acc + (rc.2 • rowRhsPoly (allRows.getD rc.1 RowKind.norm)))
                  accP) := by
      intro cs
      induction cs with
      | nil =>
          intro accR accP hacc
          simpa using hacc
      | cons rc cs ih =>
          intro accR accP hacc
          have hstep :
              fR accR rc =
                Poly3.eval (pVal μ) (tVal μ) 0
                  (accP + (rc.2 • rowRhsPoly (allRows.getD rc.1 RowKind.norm))) := by
            simp [fR, hacc, Poly3.eval_add, Poly3.eval_smul]
          calc
            (rc :: cs).foldl fR accR = cs.foldl fR (fR accR rc) := by simp [List.foldl]
            _ =
                Poly3.eval (pVal μ) (tVal μ) 0
                  (cs.foldl
                    (fun acc rc => acc + (rc.2 • rowRhsPoly (allRows.getD rc.1 RowKind.norm)))
                    (accP + (rc.2 • rowRhsPoly (allRows.getD rc.1 RowKind.norm)))) := by
                  exact ih _ _ hstep
            _ =
                Poly3.eval (pVal μ) (tVal μ) 0
                  ((rc :: cs).foldl
                    (fun acc rc => acc + (rc.2 • rowRhsPoly (allRows.getD rc.1 RowKind.norm)))
                    accP) := by
                  simp [List.foldl]
    simpa [certPoly] using hAux cert 0 0 (by simp [Poly3.eval_const])
  simpa [certLhsProb, fL] using hRows.trans hEval

private lemma certificateMatches_forall (pref : String) (cert : List (Nat × ℚ))
    (hmatch : certificateMatches pref cert = true) :
    ∀ w ∈ words14, certCoeffAt cert w = targetCoeff pref w := by
  have hAll :
      words14.all (fun w => decide (certCoeffAt cert w = targetCoeff pref w)) = true := by
    simpa [certificateMatches] using hmatch
  exact
    (List.all_iff_forall_prop (l := words14)
      (p := fun w => certCoeffAt cert w = targetCoeff pref w)).1 (by simpa using hAll)

private theorem prob_prefix_eq_sum_targetCoeff (μ : Measure FiniteDependence.MIS.State)
    [IsProbabilityMeasure μ] {m : Nat} {x : String}
    (hx : x ∈ K5Data.allowedWords m) (hm : m ≤ 14) :
    FiniteDependence.MIS.Model.prob μ (cylStr (a := (0 : ℤ)) x) =
      ∑ w ∈ allowedWordsFinset 14, (targetCoeff x w : ℝ) *
        FiniteDependence.MIS.Model.prob μ (cylStr (a := (0 : ℤ)) w) := by
  have hx01 : Is01String x := is01_of_mem_allowedWords hx
  have hxLen : x.length = m := length_of_mem_allowedWords (L := m) (s := x) hx
  have hpref :
      FiniteDependence.MIS.Model.prob μ (cylStr (a := (0 : ℤ)) x) =
        ∑ w ∈ (allowedWordsFinset 14).filter (fun w => prefixOf w m = x),
          FiniteDependence.MIS.Model.prob μ (cylStr (a := (0 : ℤ)) w) := by
    simpa using
      (prob_prefix_eq_sum (μ := μ) (a := (0 : ℤ)) (L := 14) (m := m) (hL := by decide)
        (hm := hm) (x := x) hx01 hxLen)
  have hIndicator :
      (∑ w ∈ allowedWordsFinset 14, (targetCoeff x w : ℝ) *
          FiniteDependence.MIS.Model.prob μ (cylStr (a := (0 : ℤ)) w)) =
        ∑ w ∈ (allowedWordsFinset 14).filter (fun w => prefixOf w m = x),
          FiniteDependence.MIS.Model.prob μ (cylStr (a := (0 : ℤ)) w) := by
    calc
      (∑ w ∈ allowedWordsFinset 14, (targetCoeff x w : ℝ) *
            FiniteDependence.MIS.Model.prob μ (cylStr (a := (0 : ℤ)) w)) =
          (∑ w ∈ allowedWordsFinset 14,
            (if prefixOf w m = x then (1 : ℝ) else 0) *
              FiniteDependence.MIS.Model.prob μ (cylStr (a := (0 : ℤ)) w)) := by
            refine Finset.sum_congr rfl ?_
            intro w hw
            by_cases hpre : prefixOf w m = x
            · simp [targetCoeff, hxLen, hpre]
            · simp [targetCoeff, hxLen, hpre]
      _ =
          (∑ w ∈ allowedWordsFinset 14,
            if prefixOf w m = x
              then FiniteDependence.MIS.Model.prob μ (cylStr (a := (0 : ℤ)) w) else 0) := by
            simp
      _ =
          ∑ w ∈ (allowedWordsFinset 14).filter (fun w => prefixOf w m = x),
            FiniteDependence.MIS.Model.prob μ (cylStr (a := (0 : ℤ)) w) := by
            simpa [Finset.sum_filter]
  exact hpref.trans hIndicator.symm

theorem prob_prefix_eq_eval_certPoly (μ : Measure FiniteDependence.MIS.State)
    [IsProbabilityMeasure μ] (hstat : Stationary μ) (hdep : KDependent 5 μ)
    {m : Nat} {x : String} (hx : x ∈ K5Data.allowedWords m) (hm : m ≤ 14)
    (cert : List (Nat × ℚ)) (hmatch : certificateMatches x cert = true) :
    FiniteDependence.MIS.Model.prob μ (cylStr (a := (0 : ℤ)) x) =
      Poly3.eval (pVal μ) (tVal μ) 0 (certPoly cert) := by
  have hPrefixTarget :
      FiniteDependence.MIS.Model.prob μ (cylStr (a := (0 : ℤ)) x) =
        ∑ w ∈ allowedWordsFinset 14, (targetCoeff x w : ℝ) *
          FiniteDependence.MIS.Model.prob μ (cylStr (a := (0 : ℤ)) w) :=
    prob_prefix_eq_sum_targetCoeff (μ := μ) hx hm
  have hForall := certificateMatches_forall (pref := x) (cert := cert) hmatch
  have hCoeffSum :
      (∑ w ∈ allowedWordsFinset 14, (targetCoeff x w : ℝ) *
          FiniteDependence.MIS.Model.prob μ (cylStr (a := (0 : ℤ)) w)) =
        (∑ w ∈ allowedWordsFinset 14, (certCoeffAt cert w : ℝ) *
          FiniteDependence.MIS.Model.prob μ (cylStr (a := (0 : ℤ)) w)) := by
    refine Finset.sum_congr rfl ?_
    intro w hw
    have hw14 : w ∈ K5Data.allowedWords 14 := (mem_allowedWordsFinset_iff (L := 14) (s := w)).1 hw
    have hwList : w ∈ words14 := by
      simpa [words14] using hw14
    have hEq : certCoeffAt cert w = targetCoeff x w := hForall w hwList
    simp [hEq]
  have hCertSum :
      certLhsProb μ cert =
        ∑ w ∈ allowedWordsFinset 14, (certCoeffAt cert w : ℝ) *
          FiniteDependence.MIS.Model.prob μ (cylStr (a := (0 : ℤ)) w) :=
    certLhsProb_eq_sum_certCoeffAt (μ := μ) cert
  have hCertEval :
      certLhsProb μ cert = Poly3.eval (pVal μ) (tVal μ) 0 (certPoly cert) :=
    certLhsProb_eq_eval_certPoly (μ := μ) hstat hdep cert
  calc
    FiniteDependence.MIS.Model.prob μ (cylStr (a := (0 : ℤ)) x) =
      ∑ w ∈ allowedWordsFinset 14, (targetCoeff x w : ℝ) *
        FiniteDependence.MIS.Model.prob μ (cylStr (a := (0 : ℤ)) w) := hPrefixTarget
    _ =
      ∑ w ∈ allowedWordsFinset 14, (certCoeffAt cert w : ℝ) *
        FiniteDependence.MIS.Model.prob μ (cylStr (a := (0 : ℤ)) w) := hCoeffSum
    _ = certLhsProb μ cert := hCertSum.symm
    _ = Poly3.eval (pVal μ) (tVal μ) 0 (certPoly cert) := hCertEval

end Step3

end

end Model

end K5Bridge

end FiniteDependence.MIS
