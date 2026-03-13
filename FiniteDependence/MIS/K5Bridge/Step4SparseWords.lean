import FiniteDependence.MIS.K5Bridge.Step2SparsePolys
import FiniteDependence.MIS.K5Bridge.SparseCertTables
import FiniteDependence.MIS.K5Bridge.StepLemmas

namespace FiniteDependence.MIS

namespace K5Bridge

open MeasureTheory Set
open scoped ProbabilityTheory

namespace Model

open FiniteDependence.MIS.Model

noncomputable section

namespace Step4Sparse

open Step3 Step2Sparse

private lemma mem_allowedWords_of_finset {L : Nat} {s : String} (hs : s ∈ allowedWordsFinset L) :
    s ∈ K5Data.allowedWords L :=
  (mem_allowedWordsFinset_iff (L := L) (s := s)).1 hs

private def cert_001010010100 : List (Nat × ℚ) :=
  [(66, (-1 : ℚ)), (178, (1 : ℚ))]

private theorem cert_001010010100_matches :
    certificateMatches "001010010100" cert_001010010100 = true := by
  rw [certificateMatches, words14_eq_explicit]
  simp [cert_001010010100, certCoeffAt, targetCoeff, rowCoeff]

private def cert_0101010010101 : List (Nat × ℚ) :=
  [(86, (-1 : ℚ)), (87, (-1 : ℚ)), (225, (1 : ℚ)), (255, (1 : ℚ))]

private theorem cert_0101010010101_matches :
    certificateMatches "0101010010101" cert_0101010010101 = true := by
  rw [certificateMatches, words14_eq_explicit]
  simp [cert_0101010010101, certCoeffAt, targetCoeff, rowCoeff]

private def poly_001010010100 : Poly3.Poly :=
  ((4 : ℚ) • (pPoly ^ 3)) + ((2 : ℚ) • (pPoly ^ 2)) + ((-4 : ℚ) • (pPoly * tPoly)) +
    ((-4 : ℚ) • pPoly) + ((2 : ℚ) • tPoly) + ((1 : ℚ) • (1 : Poly3.Poly))

private theorem certPoly_001010010100_eq :
    ∀ p t : ℝ, Poly3.eval p t 0 (certPoly cert_001010010100) = Poly3.eval p t 0 poly_001010010100 := by
  intro p t
  simp [words7_eq_explicit, poly_001010010100, cert_001010010100, certPoly, rowRhsPoly,
    shortMargPoly, dist7Poly, pPoly, tPoly, Poly3.eval_add, Poly3.eval_sub, Poly3.eval_mul,
    Poly3.eval_smul, Poly3.eval_pow, Poly3.eval_varP, Poly3.eval_varT, Poly3.eval_const]
  ring_nf

private def poly_0101010010101 : Poly3.Poly :=
  ((4 : ℚ) • (pPoly ^ 3)) + ((9 : ℚ) • (pPoly ^ 2)) + ((-4 : ℚ) • (pPoly * tPoly)) +
    ((-4 : ℚ) • pPoly)

private theorem certPoly_0101010010101_eq :
    ∀ p t : ℝ, Poly3.eval p t 0 (certPoly cert_0101010010101) = Poly3.eval p t 0 poly_0101010010101 := by
  intro p t
  simp [words7_eq_explicit, poly_0101010010101, cert_0101010010101, certPoly, rowRhsPoly,
    shortMargPoly, dist7Poly, pPoly, tPoly, Poly3.eval_add, Poly3.eval_sub, Poly3.eval_mul,
    Poly3.eval_smul, Poly3.eval_pow, Poly3.eval_varP, Poly3.eval_varT, Poly3.eval_const]
  ring_nf

theorem prob_001010010100_eq_formula (μ : Measure FiniteDependence.MIS.State) [IsProbabilityMeasure μ]
    (hstat : Stationary μ) (hdep : KDependent 5 μ) :
    FiniteDependence.MIS.Model.prob μ (cylStr (a := (0 : ℤ)) "001010010100") =
      (2 * pVal μ - 1) * (2 * (pVal μ) ^ 2 + 2 * (pVal μ) - 2 * (tVal μ) - 1) := by
  have hcert :
      FiniteDependence.MIS.Model.prob μ (cylStr (a := (0 : ℤ)) "001010010100") =
        Poly3.eval (pVal μ) (tVal μ) 0 (certPoly cert_001010010100) := by
    simpa using
      prob_prefix_eq_eval_certPoly (μ := μ) hstat hdep
        (m := 12) (x := "001010010100")
        (hx := mem_allowedWords_of_finset (by decide : ("001010010100" : String) ∈ allowedWordsFinset 12))
        (hm := by decide)
        (cert := cert_001010010100)
        (hmatch := cert_001010010100_matches)
  calc
    FiniteDependence.MIS.Model.prob μ (cylStr (a := (0 : ℤ)) "001010010100") =
        Poly3.eval (pVal μ) (tVal μ) 0 (certPoly cert_001010010100) := hcert
    _ = Poly3.eval (pVal μ) (tVal μ) 0 poly_001010010100 := by
          simpa using certPoly_001010010100_eq (p := pVal μ) (t := tVal μ)
    _ = (2 * pVal μ - 1) * (2 * (pVal μ) ^ 2 + 2 * (pVal μ) - 2 * (tVal μ) - 1) := by
          simp [poly_001010010100, pPoly, tPoly, Poly3.eval_add, Poly3.eval_sub, Poly3.eval_mul,
            Poly3.eval_smul, Poly3.eval_pow, Poly3.eval_varP, Poly3.eval_varT, Poly3.eval_const]
          ring_nf

theorem prob_0101010010101_eq_formula (μ : Measure FiniteDependence.MIS.State) [IsProbabilityMeasure μ]
    (hstat : Stationary μ) (hdep : KDependent 5 μ) :
    FiniteDependence.MIS.Model.prob μ (cylStr (a := (0 : ℤ)) "0101010010101") =
      pVal μ * (4 * (pVal μ) ^ 2 + 9 * (pVal μ) - 4 * (tVal μ) - 4) := by
  have hcert :
      FiniteDependence.MIS.Model.prob μ (cylStr (a := (0 : ℤ)) "0101010010101") =
        Poly3.eval (pVal μ) (tVal μ) 0 (certPoly cert_0101010010101) := by
    simpa using
      prob_prefix_eq_eval_certPoly (μ := μ) hstat hdep
        (m := 13) (x := "0101010010101")
        (hx := mem_allowedWords_of_finset (by decide : ("0101010010101" : String) ∈ allowedWordsFinset 13))
        (hm := by decide)
        (cert := cert_0101010010101)
        (hmatch := cert_0101010010101_matches)
  calc
    FiniteDependence.MIS.Model.prob μ (cylStr (a := (0 : ℤ)) "0101010010101") =
        Poly3.eval (pVal μ) (tVal μ) 0 (certPoly cert_0101010010101) := hcert
    _ = Poly3.eval (pVal μ) (tVal μ) 0 poly_0101010010101 := by
          simpa using certPoly_0101010010101_eq (p := pVal μ) (t := tVal μ)
    _ = pVal μ * (4 * (pVal μ) ^ 2 + 9 * (pVal μ) - 4 * (tVal μ) - 4) := by
          simp [poly_0101010010101, pPoly, tPoly, Poly3.eval_add, Poly3.eval_sub, Poly3.eval_mul,
            Poly3.eval_smul, Poly3.eval_pow, Poly3.eval_varP, Poly3.eval_varT, Poly3.eval_const]
          ring_nf

private def poly_101 : Poly3.Poly :=
  ((3 : ℚ) • pPoly) + ((-1 : ℚ) • (1 : Poly3.Poly))

private theorem certPoly_101_eq :
    ∀ p t : ℝ, Poly3.eval p t 0 (certPoly cert_101) = Poly3.eval p t 0 poly_101 := by
  intro p t
  simpa [poly_101, Step2Sparse.poly_101] using
    (Step2Sparse.certPoly_101_eq (p := p) (t := t) :
      Poly3.eval p t 0 (certPoly cert_101) = Poly3.eval p t 0 Step2Sparse.poly_101)

private def poly_0010100 : Poly3.Poly :=
  ((-2 : ℚ) • (pPoly ^ 2)) + ((-7 : ℚ) • pPoly) + ((3 : ℚ) • tPoly) + ((3 : ℚ) • (1 : Poly3.Poly))

private theorem certPoly_0010100_eq :
    ∀ p t : ℝ, Poly3.eval p t 0 (certPoly cert_0010100) = Poly3.eval p t 0 poly_0010100 := by
  intro p t
  simpa [poly_0010100, Step2Sparse.poly_0010100] using
    (Step2Sparse.certPoly_0010100_eq (p := p) (t := t) :
      Poly3.eval p t 0 (certPoly cert_0010100) = Poly3.eval p t 0 Step2Sparse.poly_0010100)

private def poly_10100 : Poly3.Poly :=
  ((-1 : ℚ) • (pPoly ^ 2)) + ((-2 : ℚ) • pPoly) + tPoly + ((1 : ℚ) • (1 : Poly3.Poly))

private theorem certPoly_10100_eq :
    ∀ p t : ℝ, Poly3.eval p t 0 (certPoly cert_10100) = Poly3.eval p t 0 poly_10100 := by
  intro p t
  simpa [poly_10100, Step2Sparse.poly_10100] using
    (Step2Sparse.certPoly_10100_eq (p := p) (t := t) :
      Poly3.eval p t 0 (certPoly cert_10100) = Poly3.eval p t 0 Step2Sparse.poly_10100)

private def poly_00100 : Poly3.Poly :=
  (pPoly ^ 2) + ((-1 : ℚ) • tPoly)

private theorem certPoly_00100_eq :
    ∀ p t : ℝ, Poly3.eval p t 0 (certPoly cert_00100) = Poly3.eval p t 0 poly_00100 := by
  intro p t
  simpa [poly_00100, Step2Sparse.poly_00100] using
    (Step2Sparse.certPoly_00100_eq (p := p) (t := t) :
      Poly3.eval p t 0 (certPoly cert_00100) = Poly3.eval p t 0 Step2Sparse.poly_00100)

private def poly_10100101 : Poly3.Poly :=
  ((-1 : ℚ) • (pPoly ^ 2)) + ((-10 : ℚ) • pPoly) + ((4 : ℚ) • tPoly) + ((4 : ℚ) • (1 : Poly3.Poly))

private theorem certPoly_10100101_eq :
    ∀ p t : ℝ, Poly3.eval p t 0 (certPoly cert_10100101) = Poly3.eval p t 0 poly_10100101 := by
  intro p t
  simpa [poly_10100101, Step2Sparse.poly_10100101] using
    (Step2Sparse.certPoly_10100101_eq (p := p) (t := t) :
      Poly3.eval p t 0 (certPoly cert_10100101) = Poly3.eval p t 0 Step2Sparse.poly_10100101)

private def poly_00 : Poly3.Poly :=
  ((-2 : ℚ) • pPoly) + ((1 : ℚ) • (1 : Poly3.Poly))

private theorem certPoly_00_eq :
    ∀ p t : ℝ, Poly3.eval p t 0 (certPoly cert_00) = Poly3.eval p t 0 poly_00 := by
  intro p t
  simpa [poly_00, Step2Sparse.poly_00] using
    (Step2Sparse.certPoly_00_eq (p := p) (t := t) :
      Poly3.eval p t 0 (certPoly cert_00) = Poly3.eval p t 0 Step2Sparse.poly_00)

private theorem prob_101_eq_formula (μ : Measure FiniteDependence.MIS.State) [IsProbabilityMeasure μ]
    (hstat : Stationary μ) (hdep : KDependent 5 μ) :
    FiniteDependence.MIS.Model.prob μ (cylStr (a := (0 : ℤ)) "101") = 3 * pVal μ - 1 := by
  have h := prob_101_eq_eval (μ := μ) hstat hdep
  calc
    FiniteDependence.MIS.Model.prob μ (cylStr (a := (0 : ℤ)) "101") =
        Poly3.eval (pVal μ) (tVal μ) 0 (certPoly cert_101) := h
    _ = Poly3.eval (pVal μ) (tVal μ) 0 poly_101 := by
          simpa using certPoly_101_eq (p := pVal μ) (t := tVal μ)
    _ = 3 * pVal μ - 1 := by
          simp [poly_101, pPoly, tPoly, Poly3.eval_add, Poly3.eval_sub, Poly3.eval_mul, Poly3.eval_smul,
            Poly3.eval_pow, Poly3.eval_varP, Poly3.eval_varT, Poly3.eval_const]
          ring_nf

private theorem prob_0010100_eq_formula (μ : Measure FiniteDependence.MIS.State) [IsProbabilityMeasure μ]
    (hstat : Stationary μ) (hdep : KDependent 5 μ) :
    FiniteDependence.MIS.Model.prob μ (cylStr (a := (0 : ℤ)) "0010100") =
      (-2) * (pVal μ) ^ 2 + (-7) * pVal μ + 3 * tVal μ + 3 := by
  have h := prob_0010100_eq_eval (μ := μ) hstat hdep
  calc
    FiniteDependence.MIS.Model.prob μ (cylStr (a := (0 : ℤ)) "0010100") =
        Poly3.eval (pVal μ) (tVal μ) 0 (certPoly cert_0010100) := h
    _ = Poly3.eval (pVal μ) (tVal μ) 0 poly_0010100 := by
          simpa using certPoly_0010100_eq (p := pVal μ) (t := tVal μ)
    _ = (-2) * (pVal μ) ^ 2 + (-7) * pVal μ + 3 * tVal μ + 3 := by
          simp [poly_0010100, pPoly, tPoly, Poly3.eval_add, Poly3.eval_sub, Poly3.eval_mul, Poly3.eval_smul,
            Poly3.eval_pow, Poly3.eval_varP, Poly3.eval_varT, Poly3.eval_const]

private theorem prob_10100_eq_formula (μ : Measure FiniteDependence.MIS.State) [IsProbabilityMeasure μ]
    (hstat : Stationary μ) (hdep : KDependent 5 μ) :
    FiniteDependence.MIS.Model.prob μ (cylStr (a := (0 : ℤ)) "10100") =
      (-1) * (pVal μ) ^ 2 + (-2) * pVal μ + tVal μ + 1 := by
  have h := prob_10100_eq_eval (μ := μ) hstat hdep
  calc
    FiniteDependence.MIS.Model.prob μ (cylStr (a := (0 : ℤ)) "10100") =
        Poly3.eval (pVal μ) (tVal μ) 0 (certPoly cert_10100) := h
    _ = Poly3.eval (pVal μ) (tVal μ) 0 poly_10100 := by
          simpa using certPoly_10100_eq (p := pVal μ) (t := tVal μ)
    _ = (-1) * (pVal μ) ^ 2 + (-2) * pVal μ + tVal μ + 1 := by
          simp [poly_10100, pPoly, tPoly, Poly3.eval_add, Poly3.eval_sub, Poly3.eval_mul, Poly3.eval_smul,
            Poly3.eval_pow, Poly3.eval_varP, Poly3.eval_varT, Poly3.eval_const]

private theorem prob_00100_eq_formula (μ : Measure FiniteDependence.MIS.State) [IsProbabilityMeasure μ]
    (hstat : Stationary μ) (hdep : KDependent 5 μ) :
    FiniteDependence.MIS.Model.prob μ (cylStr (a := (0 : ℤ)) "00100") =
      (pVal μ) ^ 2 - tVal μ := by
  have h := prob_00100_eq_eval (μ := μ) hstat hdep
  calc
    FiniteDependence.MIS.Model.prob μ (cylStr (a := (0 : ℤ)) "00100") =
        Poly3.eval (pVal μ) (tVal μ) 0 (certPoly cert_00100) := h
    _ = Poly3.eval (pVal μ) (tVal μ) 0 poly_00100 := by
          simpa using certPoly_00100_eq (p := pVal μ) (t := tVal μ)
    _ = (pVal μ) ^ 2 - tVal μ := by
          simp [poly_00100, pPoly, tPoly, Poly3.eval_add, Poly3.eval_sub, Poly3.eval_mul, Poly3.eval_smul,
            Poly3.eval_pow, Poly3.eval_varP, Poly3.eval_varT, Poly3.eval_const]
          ring

private theorem prob_10100101_eq_formula (μ : Measure FiniteDependence.MIS.State) [IsProbabilityMeasure μ]
    (hstat : Stationary μ) (hdep : KDependent 5 μ) :
    FiniteDependence.MIS.Model.prob μ (cylStr (a := (0 : ℤ)) "10100101") =
      (-1) * (pVal μ) ^ 2 + (-10) * pVal μ + 4 * tVal μ + 4 := by
  have h := prob_10100101_eq_eval (μ := μ) hstat hdep
  calc
    FiniteDependence.MIS.Model.prob μ (cylStr (a := (0 : ℤ)) "10100101") =
        Poly3.eval (pVal μ) (tVal μ) 0 (certPoly cert_10100101) := h
    _ = Poly3.eval (pVal μ) (tVal μ) 0 poly_10100101 := by
          simpa using certPoly_10100101_eq (p := pVal μ) (t := tVal μ)
    _ = (-1) * (pVal μ) ^ 2 + (-10) * pVal μ + 4 * tVal μ + 4 := by
          simp [poly_10100101, pPoly, tPoly, Poly3.eval_add, Poly3.eval_sub, Poly3.eval_mul, Poly3.eval_smul,
            Poly3.eval_pow, Poly3.eval_varP, Poly3.eval_varT, Poly3.eval_const]

private theorem prob_00_eq_formula (μ : Measure FiniteDependence.MIS.State) [IsProbabilityMeasure μ]
    (hstat : Stationary μ) (hdep : KDependent 5 μ) :
    FiniteDependence.MIS.Model.prob μ (cylStr (a := (0 : ℤ)) "00") = 1 - 2 * pVal μ := by
  have h := prob_00_eq_eval (μ := μ) hstat hdep
  calc
    FiniteDependence.MIS.Model.prob μ (cylStr (a := (0 : ℤ)) "00") =
        Poly3.eval (pVal μ) (tVal μ) 0 (certPoly cert_00) := h
    _ = Poly3.eval (pVal μ) (tVal μ) 0 poly_00 := by
          simpa using certPoly_00_eq (p := pVal μ) (t := tVal μ)
    _ = 1 - 2 * pVal μ := by
          simp [poly_00, pPoly, tPoly, Poly3.eval_add, Poly3.eval_sub, Poly3.eval_mul, Poly3.eval_smul,
            Poly3.eval_pow, Poly3.eval_varP, Poly3.eval_varT, Poly3.eval_const]
          ring_nf

set_option maxHeartbeats 20000000 in
theorem prob_101010010010100_eq_formula (μ : Measure FiniteDependence.MIS.State) [IsProbabilityMeasure μ]
    (hstat : Stationary μ) (hdep : KDependent 5 μ) :
    FiniteDependence.MIS.Model.prob μ (cylStr (a := (0 : ℤ)) "101010010010100") =
      (-1) * (pVal μ) ^ 4 + (-10) * (pVal μ) ^ 3 + 2 * (pVal μ) ^ 2 * tVal μ +
        (-37) * (pVal μ) ^ 2 + 19 * pVal μ * tVal μ + 34 * pVal μ -
        (tVal μ) ^ 2 + (-8) * tVal μ + (-7) := by
  have h101_mem : ("101" : String) ∈ K5Data.allowedWords 3 :=
    mem_allowedWords_of_finset (by decide : ("101" : String) ∈ allowedWordsFinset 3)
  have h0010100_mem : ("0010100" : String) ∈ K5Data.allowedWords 7 :=
    mem_allowedWords_of_finset (by decide : ("0010100" : String) ∈ allowedWordsFinset 7)
  have h10100_mem : ("10100" : String) ∈ K5Data.allowedWords 5 :=
    mem_allowedWords_of_finset (by decide : ("10100" : String) ∈ allowedWordsFinset 5)
  have h00100_mem : ("00100" : String) ∈ K5Data.allowedWords 5 :=
    mem_allowedWords_of_finset (by decide : ("00100" : String) ∈ allowedWordsFinset 5)
  have h10100101_mem : ("10100101" : String) ∈ K5Data.allowedWords 8 :=
    mem_allowedWords_of_finset (by decide : ("10100101" : String) ∈ allowedWordsFinset 8)
  have h00_mem : ("00" : String) ∈ K5Data.allowedWords 2 :=
    mem_allowedWords_of_finset (by decide : ("00" : String) ∈ allowedWordsFinset 2)

  have h101_01 : Is01String ("101" : String) := Is01String.of_mem_allowedWords (L := 3) h101_mem
  have h0010100_01 : Is01String ("0010100" : String) := Is01String.of_mem_allowedWords (L := 7) h0010100_mem
  have h10100_01 : Is01String ("10100" : String) := Is01String.of_mem_allowedWords (L := 5) h10100_mem
  have h00100_01 : Is01String ("00100" : String) := Is01String.of_mem_allowedWords (L := 5) h00100_mem
  have h10100101_01 : Is01String ("10100101" : String) := Is01String.of_mem_allowedWords (L := 8) h10100101_mem
  have h00_01 : Is01String ("00" : String) := Is01String.of_mem_allowedWords (L := 2) h00_mem

  have hrow1 :
      FiniteDependence.MIS.Model.prob μ (cylStr (a := (0 : ℤ)) "101") *
          FiniteDependence.MIS.Model.prob μ (cylStr (a := (0 : ℤ)) "0010100") =
        FiniteDependence.MIS.Model.prob μ (cylStr (a := (0 : ℤ)) "101001010010100") +
          FiniteDependence.MIS.Model.prob μ (cylStr (a := (0 : ℤ)) "101010010010100") := by
    have hsplit := prob_prod_gap5 (μ := μ) hstat hdep
      (m := 3) (n := 7) (x := ("101" : String)) (y := ("0010100" : String))
      h101_01 h0010100_01 (by decide) (by decide)
    have hS :
        (allowedWordsFinset (3 + 5 + 7)).filter
            (fun w => prefixOf w 3 = ("101" : String) ∧ suffixFrom w (3 + 5) = ("0010100" : String)) =
          ({("101001010010100" : String), "101010010010100"} : Finset String) := by
      have h3 :
          (allowedWordsFinset 3).filter (fun w => prefixOf w 3 = ("101" : String)) =
            ({("101" : String)} : Finset String) :=
        filter_prefix_exact (by decide : ("101" : String) ∈ allowedWordsFinset 3)
      have h4 :
          (allowedWordsFinset 4).filter (fun w => prefixOf w 3 = ("101" : String)) =
            ({("1010" : String)} : Finset String) := by
        rw [filter_prefix_step (m := 3) (n := 2) (x := ("101" : String)) (by decide), h3]
        decide
      have h5 :
          (allowedWordsFinset 5).filter (fun w => prefixOf w 3 = ("101" : String)) =
            ({("10100" : String), "10101"} : Finset String) := by
        rw [filter_prefix_step (m := 3) (n := 3) (x := ("101" : String)) (by decide), h4]
        decide
      have h6 :
          (allowedWordsFinset 6).filter (fun w => prefixOf w 3 = ("101" : String)) =
            ({("101001" : String), "101010"} : Finset String) := by
        rw [filter_prefix_step (m := 3) (n := 4) (x := ("101" : String)) (by decide), h5]
        decide
      have h7 :
          (allowedWordsFinset 7).filter (fun w => prefixOf w 3 = ("101" : String)) =
            ({("1010010" : String), "1010100", "1010101"} : Finset String) := by
        rw [filter_prefix_step (m := 3) (n := 5) (x := ("101" : String)) (by decide), h6]
        decide
      have h8 :
          (allowedWordsFinset 8).filter (fun w => prefixOf w 3 = ("101" : String)) =
            ({("10100100" : String), "10100101", "10101001", "10101010"} : Finset String) := by
        rw [filter_prefix_step (m := 3) (n := 6) (x := ("101" : String)) (by decide), h7]
        decide
      have h8_empty :
          (allowedWordsFinset 8).filter
              (fun w => prefixOf w 3 = ("101" : String) ∧ suffixFrom w 8 = ("" : String)) =
            ({("10100100" : String), "10100101", "10101001", "10101010"} : Finset String) := by
        rw [filter_pref_suf_empty (m := 3) (L := 8) (x := ("101" : String)) (by decide), h8]
      have h9 :
          (allowedWordsFinset 9).filter
              (fun w => prefixOf w 3 = ("101" : String) ∧ suffixFrom w 8 = ("0" : String)) =
            ({("101001010" : String), "101010010", "101010100"} : Finset String) := by
        rw [show
          (allowedWordsFinset 9).filter
              (fun w => prefixOf w 3 = ("101" : String) ∧ suffixFrom w 8 = ("0" : String)) =
            (((allowedWordsFinset 8).filter
                (fun w => prefixOf w 3 = ("101" : String) ∧ suffixFrom w 8 = ("" : String))).biUnion
              fun w => ((K5Data.extensions w).toFinset).filter
                (fun s => suffixFrom s 8 = ("0" : String))) from by
              simpa using
                (filter_pref_suf_step (m := 3) (n := 7) (x := ("101" : String)) (u := ("" : String))
                  (c := '0') (by decide) (by decide))]
        rw [h8_empty]
        decide
      have h10 :
          (allowedWordsFinset 10).filter
              (fun w => prefixOf w 3 = ("101" : String) ∧ suffixFrom w 8 = ("00" : String)) =
            ({("1010010100" : String), "1010100100"} : Finset String) := by
        rw [show
          (allowedWordsFinset 10).filter
              (fun w => prefixOf w 3 = ("101" : String) ∧ suffixFrom w 8 = ("00" : String)) =
            (((allowedWordsFinset 9).filter
                (fun w => prefixOf w 3 = ("101" : String) ∧ suffixFrom w 8 = ("0" : String))).biUnion
              fun w => ((K5Data.extensions w).toFinset).filter
                (fun s => suffixFrom s 8 = ("00" : String))) from by
              simpa using
                (filter_pref_suf_step (m := 3) (n := 8) (x := ("101" : String)) (u := ("0" : String))
                  (c := '0') (by decide) (by decide))]
        rw [h9]
        decide
      have h11 :
          (allowedWordsFinset 11).filter
              (fun w => prefixOf w 3 = ("101" : String) ∧ suffixFrom w 8 = ("001" : String)) =
            ({("10100101001" : String), "10101001001"} : Finset String) := by
        rw [show
          (allowedWordsFinset 11).filter
              (fun w => prefixOf w 3 = ("101" : String) ∧ suffixFrom w 8 = ("001" : String)) =
            (((allowedWordsFinset 10).filter
                (fun w => prefixOf w 3 = ("101" : String) ∧ suffixFrom w 8 = ("00" : String))).biUnion
              fun w => ((K5Data.extensions w).toFinset).filter
                (fun s => suffixFrom s 8 = ("001" : String))) from by
              simpa using
                (filter_pref_suf_step (m := 3) (n := 9) (x := ("101" : String)) (u := ("00" : String))
                  (c := '1') (by decide) (by decide))]
        rw [h10]
        decide
      have h12 :
          (allowedWordsFinset 12).filter
              (fun w => prefixOf w 3 = ("101" : String) ∧ suffixFrom w 8 = ("0010" : String)) =
            ({("101001010010" : String), "101010010010"} : Finset String) := by
        rw [show
          (allowedWordsFinset 12).filter
              (fun w => prefixOf w 3 = ("101" : String) ∧ suffixFrom w 8 = ("0010" : String)) =
            (((allowedWordsFinset 11).filter
                (fun w => prefixOf w 3 = ("101" : String) ∧ suffixFrom w 8 = ("001" : String))).biUnion
              fun w => ((K5Data.extensions w).toFinset).filter
                (fun s => suffixFrom s 8 = ("0010" : String))) from by
              simpa using
                (filter_pref_suf_step (m := 3) (n := 10) (x := ("101" : String)) (u := ("001" : String))
                  (c := '0') (by decide) (by decide))]
        rw [h11]
        decide
      have h13 :
          (allowedWordsFinset 13).filter
              (fun w => prefixOf w 3 = ("101" : String) ∧ suffixFrom w 8 = ("00101" : String)) =
            ({("1010010100101" : String), "1010100100101"} : Finset String) := by
        rw [show
          (allowedWordsFinset 13).filter
              (fun w => prefixOf w 3 = ("101" : String) ∧ suffixFrom w 8 = ("00101" : String)) =
            (((allowedWordsFinset 12).filter
                (fun w => prefixOf w 3 = ("101" : String) ∧ suffixFrom w 8 = ("0010" : String))).biUnion
              fun w => ((K5Data.extensions w).toFinset).filter
                (fun s => suffixFrom s 8 = ("00101" : String))) from by
              simpa using
                (filter_pref_suf_step (m := 3) (n := 11) (x := ("101" : String)) (u := ("0010" : String))
                  (c := '1') (by decide) (by decide))]
        rw [h12]
        decide
      have h14 :
          (allowedWordsFinset 14).filter
              (fun w => prefixOf w 3 = ("101" : String) ∧ suffixFrom w 8 = ("001010" : String)) =
            ({("10100101001010" : String), "10101001001010"} : Finset String) := by
        rw [show
          (allowedWordsFinset 14).filter
              (fun w => prefixOf w 3 = ("101" : String) ∧ suffixFrom w 8 = ("001010" : String)) =
            (((allowedWordsFinset 13).filter
                (fun w => prefixOf w 3 = ("101" : String) ∧ suffixFrom w 8 = ("00101" : String))).biUnion
              fun w => ((K5Data.extensions w).toFinset).filter
                (fun s => suffixFrom s 8 = ("001010" : String))) from by
              simpa using
                (filter_pref_suf_step (m := 3) (n := 12) (x := ("101" : String)) (u := ("00101" : String))
                  (c := '0') (by decide) (by decide))]
        rw [h13]
        decide
      have h15 :
          (allowedWordsFinset 15).filter
              (fun w => prefixOf w 3 = ("101" : String) ∧ suffixFrom w 8 = ("0010100" : String)) =
            ({("101001010010100" : String), "101010010010100"} : Finset String) := by
        rw [show
          (allowedWordsFinset 15).filter
              (fun w => prefixOf w 3 = ("101" : String) ∧ suffixFrom w 8 = ("0010100" : String)) =
            (((allowedWordsFinset 14).filter
                (fun w => prefixOf w 3 = ("101" : String) ∧ suffixFrom w 8 = ("001010" : String))).biUnion
              fun w => ((K5Data.extensions w).toFinset).filter
                (fun s => suffixFrom s 8 = ("0010100" : String))) from by
              simpa using
                (filter_pref_suf_step (m := 3) (n := 13) (x := ("101" : String)) (u := ("001010" : String))
                  (c := '0') (by decide) (by decide))]
        rw [h14]
        decide
      simpa [Nat.add_assoc] using h15
    simpa [hS, add_assoc, add_left_comm, add_comm] using hsplit

  have hrow2 :
      FiniteDependence.MIS.Model.prob μ (cylStr (a := (0 : ℤ)) "10100") *
          FiniteDependence.MIS.Model.prob μ (cylStr (a := (0 : ℤ)) "00100") =
        FiniteDependence.MIS.Model.prob μ (cylStr (a := (0 : ℤ)) "101001010100100") := by
    have hsplit := prob_prod_gap5 (μ := μ) hstat hdep
      (m := 5) (n := 5) (x := ("10100" : String)) (y := ("00100" : String))
      h10100_01 h00100_01 (by decide) (by decide)
    have hS :
        (allowedWordsFinset (5 + 5 + 5)).filter
            (fun w => prefixOf w 5 = ("10100" : String) ∧ suffixFrom w (5 + 5) = ("00100" : String)) =
          ({("101001010100100" : String)} : Finset String) := by
      have h5 :
          (allowedWordsFinset 5).filter (fun w => prefixOf w 5 = ("10100" : String)) =
            ({("10100" : String)} : Finset String) :=
        filter_prefix_exact (by decide : ("10100" : String) ∈ allowedWordsFinset 5)
      have h6 :
          (allowedWordsFinset 6).filter (fun w => prefixOf w 5 = ("10100" : String)) =
            ({("101001" : String)} : Finset String) := by
        rw [filter_prefix_step (m := 5) (n := 4) (x := ("10100" : String)) (by decide), h5]
        decide
      have h7 :
          (allowedWordsFinset 7).filter (fun w => prefixOf w 5 = ("10100" : String)) =
            ({("1010010" : String)} : Finset String) := by
        rw [filter_prefix_step (m := 5) (n := 5) (x := ("10100" : String)) (by decide), h6]
        decide
      have h8 :
          (allowedWordsFinset 8).filter (fun w => prefixOf w 5 = ("10100" : String)) =
            ({("10100100" : String), "10100101"} : Finset String) := by
        rw [filter_prefix_step (m := 5) (n := 6) (x := ("10100" : String)) (by decide), h7]
        decide
      have h9 :
          (allowedWordsFinset 9).filter (fun w => prefixOf w 5 = ("10100" : String)) =
            ({("101001001" : String), "101001010"} : Finset String) := by
        rw [filter_prefix_step (m := 5) (n := 7) (x := ("10100" : String)) (by decide), h8]
        decide
      have h10 :
          (allowedWordsFinset 10).filter (fun w => prefixOf w 5 = ("10100" : String)) =
            ({("1010010010" : String), "1010010100", "1010010101"} : Finset String) := by
        rw [filter_prefix_step (m := 5) (n := 8) (x := ("10100" : String)) (by decide), h9]
        decide
      have h10_empty :
          (allowedWordsFinset 10).filter
              (fun w => prefixOf w 5 = ("10100" : String) ∧ suffixFrom w 10 = ("" : String)) =
            ({("1010010010" : String), "1010010100", "1010010101"} : Finset String) := by
        rw [filter_pref_suf_empty (m := 5) (L := 10) (x := ("10100" : String)) (by decide), h10]
      have h11 :
          (allowedWordsFinset 11).filter
              (fun w => prefixOf w 5 = ("10100" : String) ∧ suffixFrom w 10 = ("0" : String)) =
            ({("10100100100" : String), "10100101010"} : Finset String) := by
        rw [show
          (allowedWordsFinset 11).filter
              (fun w => prefixOf w 5 = ("10100" : String) ∧ suffixFrom w 10 = ("0" : String)) =
            (((allowedWordsFinset 10).filter
                (fun w => prefixOf w 5 = ("10100" : String) ∧ suffixFrom w 10 = ("" : String))).biUnion
              fun w => ((K5Data.extensions w).toFinset).filter
                (fun s => suffixFrom s 10 = ("0" : String))) from by
              simpa using
                (filter_pref_suf_step (m := 5) (n := 9) (x := ("10100" : String)) (u := ("" : String))
                  (c := '0') (by decide) (by decide))]
        rw [h10_empty]
        decide
      have h12 :
          (allowedWordsFinset 12).filter
              (fun w => prefixOf w 5 = ("10100" : String) ∧ suffixFrom w 10 = ("00" : String)) =
            ({("101001010100" : String)} : Finset String) := by
        rw [show
          (allowedWordsFinset 12).filter
              (fun w => prefixOf w 5 = ("10100" : String) ∧ suffixFrom w 10 = ("00" : String)) =
            (((allowedWordsFinset 11).filter
                (fun w => prefixOf w 5 = ("10100" : String) ∧ suffixFrom w 10 = ("0" : String))).biUnion
              fun w => ((K5Data.extensions w).toFinset).filter
                (fun s => suffixFrom s 10 = ("00" : String))) from by
              simpa using
                (filter_pref_suf_step (m := 5) (n := 10) (x := ("10100" : String)) (u := ("0" : String))
                  (c := '0') (by decide) (by decide))]
        rw [h11]
        decide
      have h13 :
          (allowedWordsFinset 13).filter
              (fun w => prefixOf w 5 = ("10100" : String) ∧ suffixFrom w 10 = ("001" : String)) =
            ({("1010010101001" : String)} : Finset String) := by
        rw [show
          (allowedWordsFinset 13).filter
              (fun w => prefixOf w 5 = ("10100" : String) ∧ suffixFrom w 10 = ("001" : String)) =
            (((allowedWordsFinset 12).filter
                (fun w => prefixOf w 5 = ("10100" : String) ∧ suffixFrom w 10 = ("00" : String))).biUnion
              fun w => ((K5Data.extensions w).toFinset).filter
                (fun s => suffixFrom s 10 = ("001" : String))) from by
              simpa using
                (filter_pref_suf_step (m := 5) (n := 11) (x := ("10100" : String)) (u := ("00" : String))
                  (c := '1') (by decide) (by decide))]
        rw [h12]
        decide
      have h14 :
          (allowedWordsFinset 14).filter
              (fun w => prefixOf w 5 = ("10100" : String) ∧ suffixFrom w 10 = ("0010" : String)) =
            ({("10100101010010" : String)} : Finset String) := by
        rw [show
          (allowedWordsFinset 14).filter
              (fun w => prefixOf w 5 = ("10100" : String) ∧ suffixFrom w 10 = ("0010" : String)) =
            (((allowedWordsFinset 13).filter
                (fun w => prefixOf w 5 = ("10100" : String) ∧ suffixFrom w 10 = ("001" : String))).biUnion
              fun w => ((K5Data.extensions w).toFinset).filter
                (fun s => suffixFrom s 10 = ("0010" : String))) from by
              simpa using
                (filter_pref_suf_step (m := 5) (n := 12) (x := ("10100" : String)) (u := ("001" : String))
                  (c := '0') (by decide) (by decide))]
        rw [h13]
        decide
      have h15 :
          (allowedWordsFinset 15).filter
              (fun w => prefixOf w 5 = ("10100" : String) ∧ suffixFrom w 10 = ("00100" : String)) =
            ({("101001010100100" : String)} : Finset String) := by
        rw [show
          (allowedWordsFinset 15).filter
              (fun w => prefixOf w 5 = ("10100" : String) ∧ suffixFrom w 10 = ("00100" : String)) =
            (((allowedWordsFinset 14).filter
                (fun w => prefixOf w 5 = ("10100" : String) ∧ suffixFrom w 10 = ("0010" : String))).biUnion
              fun w => ((K5Data.extensions w).toFinset).filter
                (fun s => suffixFrom s 10 = ("00100" : String))) from by
              simpa using
                (filter_pref_suf_step (m := 5) (n := 13) (x := ("10100" : String)) (u := ("0010" : String))
                  (c := '0') (by decide) (by decide))]
        rw [h14]
        decide
      simpa [Nat.add_assoc] using h15
    simpa [hS] using hsplit

  have hrow3 :
      FiniteDependence.MIS.Model.prob μ (cylStr (a := (0 : ℤ)) "10100101") *
          FiniteDependence.MIS.Model.prob μ (cylStr (a := (0 : ℤ)) "00") =
        FiniteDependence.MIS.Model.prob μ (cylStr (a := (0 : ℤ)) "101001010010100") +
          FiniteDependence.MIS.Model.prob μ (cylStr (a := (0 : ℤ)) "101001010100100") := by
    have hsplit := prob_prod_gap5 (μ := μ) hstat hdep
      (m := 8) (n := 2) (x := ("10100101" : String)) (y := ("00" : String))
      h10100101_01 h00_01 (by decide) (by decide)
    have hS :
        (allowedWordsFinset (8 + 5 + 2)).filter
            (fun w => prefixOf w 8 = ("10100101" : String) ∧ suffixFrom w (8 + 5) = ("00" : String)) =
          ({("101001010010100" : String), "101001010100100"} : Finset String) := by
      have h8 :
          (allowedWordsFinset 8).filter (fun w => prefixOf w 8 = ("10100101" : String)) =
            ({("10100101" : String)} : Finset String) :=
        filter_prefix_exact (by decide : ("10100101" : String) ∈ allowedWordsFinset 8)
      have h9 :
          (allowedWordsFinset 9).filter (fun w => prefixOf w 8 = ("10100101" : String)) =
            ({("101001010" : String)} : Finset String) := by
        rw [filter_prefix_step (m := 8) (n := 7) (x := ("10100101" : String)) (by decide), h8]
        decide
      have h10 :
          (allowedWordsFinset 10).filter (fun w => prefixOf w 8 = ("10100101" : String)) =
            ({("1010010100" : String), "1010010101"} : Finset String) := by
        rw [filter_prefix_step (m := 8) (n := 8) (x := ("10100101" : String)) (by decide), h9]
        decide
      have h11 :
          (allowedWordsFinset 11).filter (fun w => prefixOf w 8 = ("10100101" : String)) =
            ({("10100101001" : String), "10100101010"} : Finset String) := by
        rw [filter_prefix_step (m := 8) (n := 9) (x := ("10100101" : String)) (by decide), h10]
        decide
      have h12 :
          (allowedWordsFinset 12).filter (fun w => prefixOf w 8 = ("10100101" : String)) =
            ({("101001010010" : String), "101001010100", "101001010101"} : Finset String) := by
        rw [filter_prefix_step (m := 8) (n := 10) (x := ("10100101" : String)) (by decide), h11]
        decide
      have h13 :
          (allowedWordsFinset 13).filter (fun w => prefixOf w 8 = ("10100101" : String)) =
            ({("1010010100100" : String), "1010010100101", "1010010101001", "1010010101010"} :
              Finset String) := by
        rw [filter_prefix_step (m := 8) (n := 11) (x := ("10100101" : String)) (by decide), h12]
        decide
      have h13_empty :
          (allowedWordsFinset 13).filter
              (fun w => prefixOf w 8 = ("10100101" : String) ∧ suffixFrom w 13 = ("" : String)) =
            ({("1010010100100" : String), "1010010100101", "1010010101001", "1010010101010"} :
              Finset String) := by
        rw [filter_pref_suf_empty (m := 8) (L := 13) (x := ("10100101" : String)) (by decide), h13]
      have h14 :
          (allowedWordsFinset 14).filter
              (fun w => prefixOf w 8 = ("10100101" : String) ∧ suffixFrom w 13 = ("0" : String)) =
            ({("10100101001010" : String), "10100101010010", "10100101010100"} : Finset String) := by
        rw [show
          (allowedWordsFinset 14).filter
              (fun w => prefixOf w 8 = ("10100101" : String) ∧ suffixFrom w 13 = ("0" : String)) =
            (((allowedWordsFinset 13).filter
                (fun w => prefixOf w 8 = ("10100101" : String) ∧ suffixFrom w 13 = ("" : String))).biUnion
              fun w => ((K5Data.extensions w).toFinset).filter
                (fun s => suffixFrom s 13 = ("0" : String))) from by
              simpa using
                (filter_pref_suf_step (m := 8) (n := 12) (x := ("10100101" : String)) (u := ("" : String))
                  (c := '0') (by decide) (by decide))]
        rw [h13_empty]
        decide
      have h15 :
          (allowedWordsFinset 15).filter
              (fun w => prefixOf w 8 = ("10100101" : String) ∧ suffixFrom w 13 = ("00" : String)) =
            ({("101001010010100" : String), "101001010100100"} : Finset String) := by
        rw [show
          (allowedWordsFinset 15).filter
              (fun w => prefixOf w 8 = ("10100101" : String) ∧ suffixFrom w 13 = ("00" : String)) =
            (((allowedWordsFinset 14).filter
                (fun w => prefixOf w 8 = ("10100101" : String) ∧ suffixFrom w 13 = ("0" : String))).biUnion
              fun w => ((K5Data.extensions w).toFinset).filter
                (fun s => suffixFrom s 13 = ("00" : String))) from by
              simpa using
                (filter_pref_suf_step (m := 8) (n := 13) (x := ("10100101" : String)) (u := ("0" : String))
                  (c := '0') (by decide) (by decide))]
        rw [h14]
        decide
      simpa [Nat.add_assoc] using h15
    simpa [hS, add_assoc, add_left_comm, add_comm] using hsplit

  have hmain :
      FiniteDependence.MIS.Model.prob μ (cylStr (a := (0 : ℤ)) "101010010010100") =
        FiniteDependence.MIS.Model.prob μ (cylStr (a := (0 : ℤ)) "101") *
            FiniteDependence.MIS.Model.prob μ (cylStr (a := (0 : ℤ)) "0010100") +
          FiniteDependence.MIS.Model.prob μ (cylStr (a := (0 : ℤ)) "10100") *
            FiniteDependence.MIS.Model.prob μ (cylStr (a := (0 : ℤ)) "00100") -
          FiniteDependence.MIS.Model.prob μ (cylStr (a := (0 : ℤ)) "10100101") *
            FiniteDependence.MIS.Model.prob μ (cylStr (a := (0 : ℤ)) "00") := by
    linarith [hrow1, hrow2, hrow3]

  have h101 := prob_101_eq_formula (μ := μ) hstat hdep
  have h0010100 := prob_0010100_eq_formula (μ := μ) hstat hdep
  have h10100 := prob_10100_eq_formula (μ := μ) hstat hdep
  have h00100 := prob_00100_eq_formula (μ := μ) hstat hdep
  have h10100101 := prob_10100101_eq_formula (μ := μ) hstat hdep
  have h00 := prob_00_eq_formula (μ := μ) hstat hdep

  have hpoly :
      FiniteDependence.MIS.Model.prob μ (cylStr (a := (0 : ℤ)) "101010010010100") =
        (-1) * (pVal μ) ^ 4 + (-10) * (pVal μ) ^ 3 + 2 * (pVal μ) ^ 2 * tVal μ +
          (-37) * (pVal μ) ^ 2 + 19 * pVal μ * tVal μ + 34 * pVal μ -
          (tVal μ) ^ 2 + (-8) * tVal μ + (-7) := by
    have hmain' := hmain
    simp_rw [h101, h0010100, h10100, h00100, h10100101, h00] at hmain'
    ring_nf at hmain'
    convert hmain' using 1 <;> ring_nf
  simpa using hpoly

end Step4Sparse

end

end Model

end K5Bridge

end FiniteDependence.MIS
