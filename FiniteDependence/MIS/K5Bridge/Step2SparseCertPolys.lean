import FiniteDependence.MIS.K5Bridge.SparseCertStep2Data
import FiniteDependence.MIS.K5Bridge.SparseCertTables
import FiniteDependence.MIS.K5Bridge.Step3SparseCore

namespace FiniteDependence.MIS

namespace K5Bridge

namespace Model

noncomputable section

namespace Step2Sparse

open Step3

def poly_1 : Poly3.Poly :=
  pPoly

theorem certPoly_1_eq (p t : ℝ) :
    Poly3.eval p t 0 (certPoly cert_1) = Poly3.eval p t 0 poly_1 := by
  simp [words7_eq_explicit, poly_1, cert_1, certPoly, rowRhsPoly, shortMargPoly, dist7Poly,
    pPoly, tPoly, Poly3.eval_add, Poly3.eval_sub, Poly3.eval_mul, Poly3.eval_smul,
    Poly3.eval_pow, Poly3.eval_varP, Poly3.eval_varT, Poly3.eval_const]
  ring_nf

def poly_0010100101 : Poly3.Poly :=
  ((-4 : ℚ) • (pPoly ^ 2)) + ((-5 : ℚ) • pPoly) + ((3 : ℚ) • tPoly) +
    (((5 : ℚ) / 2) • (1 : Poly3.Poly))

theorem certPoly_0010100101_eq (p t : ℝ) :
    Poly3.eval p t 0 (certPoly cert_0010100101) = Poly3.eval p t 0 poly_0010100101 := by
  simp [words7_eq_explicit, poly_0010100101, cert_0010100101, certPoly, rowRhsPoly,
    shortMargPoly, dist7Poly, pPoly, tPoly, Poly3.eval_add, Poly3.eval_sub, Poly3.eval_mul,
    Poly3.eval_smul, Poly3.eval_pow, Poly3.eval_varP, Poly3.eval_varT, Poly3.eval_const]
  ring_nf

def poly_100 : Poly3.Poly :=
  ((-2 : ℚ) • pPoly) + ((1 : ℚ) • (1 : Poly3.Poly))

theorem certPoly_100_eq (p t : ℝ) :
    Poly3.eval p t 0 (certPoly cert_100) = Poly3.eval p t 0 poly_100 := by
  simp [words7_eq_explicit, poly_100, cert_100, certPoly, rowRhsPoly, shortMargPoly, dist7Poly,
    pPoly, tPoly, Poly3.eval_add, Poly3.eval_sub, Poly3.eval_mul, Poly3.eval_smul,
    Poly3.eval_pow, Poly3.eval_varP, Poly3.eval_varT, Poly3.eval_const]
  ring_nf

def poly_10100101 : Poly3.Poly :=
  ((-1 : ℚ) • (pPoly ^ 2)) + ((-10 : ℚ) • pPoly) + ((4 : ℚ) • tPoly) +
    ((4 : ℚ) • (1 : Poly3.Poly))

theorem certPoly_10100101_eq (p t : ℝ) :
    Poly3.eval p t 0 (certPoly cert_10100101) = Poly3.eval p t 0 poly_10100101 := by
  simp [words7_eq_explicit, poly_10100101, cert_10100101, certPoly, rowRhsPoly,
    shortMargPoly, dist7Poly, pPoly, tPoly, Poly3.eval_add, Poly3.eval_sub, Poly3.eval_mul,
    Poly3.eval_smul, Poly3.eval_pow, Poly3.eval_varP, Poly3.eval_varT, Poly3.eval_const]
  ring_nf

def poly_10100 : Poly3.Poly :=
  ((-1 : ℚ) • (pPoly ^ 2)) + ((-2 : ℚ) • pPoly) + tPoly + ((1 : ℚ) • (1 : Poly3.Poly))

theorem certPoly_10100_eq (p t : ℝ) :
    Poly3.eval p t 0 (certPoly cert_10100) = Poly3.eval p t 0 poly_10100 := by
  simp [words7_eq_explicit, poly_10100, cert_10100, certPoly, rowRhsPoly, shortMargPoly,
    dist7Poly, pPoly, tPoly, Poly3.eval_add, Poly3.eval_sub, Poly3.eval_mul, Poly3.eval_smul,
    Poly3.eval_pow, Poly3.eval_varP, Poly3.eval_varT, Poly3.eval_const]
  ring_nf

def poly_001001 : Poly3.Poly :=
  (pPoly ^ 2) + ((-1 : ℚ) • tPoly)

theorem certPoly_001001_eq (p t : ℝ) :
    Poly3.eval p t 0 (certPoly cert_001001) = Poly3.eval p t 0 poly_001001 := by
  simp [words7_eq_explicit, poly_001001, cert_001001, certPoly, rowRhsPoly, shortMargPoly,
    dist7Poly, pPoly, tPoly, Poly3.eval_add, Poly3.eval_sub, Poly3.eval_mul, Poly3.eval_smul,
    Poly3.eval_pow, Poly3.eval_varP, Poly3.eval_varT, Poly3.eval_const]
  ring_nf

def poly_100101 : Poly3.Poly :=
  poly_10100

theorem certPoly_100101_eq (p t : ℝ) :
    Poly3.eval p t 0 (certPoly cert_100101) = Poly3.eval p t 0 poly_100101 := by
  simp [words7_eq_explicit, poly_100101, poly_10100, cert_100101, certPoly, rowRhsPoly,
    shortMargPoly, dist7Poly, pPoly, tPoly, Poly3.eval_add, Poly3.eval_sub, Poly3.eval_mul,
    Poly3.eval_smul, Poly3.eval_pow, Poly3.eval_varP, Poly3.eval_varT, Poly3.eval_const]
  ring_nf

def poly_100100 : Poly3.Poly :=
  poly_001001

theorem certPoly_100100_eq (p t : ℝ) :
    Poly3.eval p t 0 (certPoly cert_100100) = Poly3.eval p t 0 poly_100100 := by
  simp [words7_eq_explicit, poly_100100, poly_001001, cert_100100, certPoly, rowRhsPoly,
    shortMargPoly, dist7Poly, pPoly, tPoly, Poly3.eval_add, Poly3.eval_sub, Poly3.eval_mul,
    Poly3.eval_smul, Poly3.eval_pow, Poly3.eval_varP, Poly3.eval_varT, Poly3.eval_const]
  ring_nf

def poly_00101 : Poly3.Poly :=
  poly_10100

theorem certPoly_00101_eq (p t : ℝ) :
    Poly3.eval p t 0 (certPoly cert_00101) = Poly3.eval p t 0 poly_00101 := by
  simp [words7_eq_explicit, poly_00101, poly_10100, cert_00101, certPoly, rowRhsPoly,
    shortMargPoly, dist7Poly, pPoly, tPoly, Poly3.eval_add, Poly3.eval_sub, Poly3.eval_mul,
    Poly3.eval_smul, Poly3.eval_pow, Poly3.eval_varP, Poly3.eval_varT, Poly3.eval_const]
  ring_nf

def poly_101 : Poly3.Poly :=
  ((3 : ℚ) • pPoly) + ((-1 : ℚ) • (1 : Poly3.Poly))

theorem certPoly_101_eq (p t : ℝ) :
    Poly3.eval p t 0 (certPoly cert_101) = Poly3.eval p t 0 poly_101 := by
  simp [words7_eq_explicit, poly_101, cert_101, certPoly, rowRhsPoly, shortMargPoly, dist7Poly,
    pPoly, tPoly, Poly3.eval_add, Poly3.eval_sub, Poly3.eval_mul, Poly3.eval_smul,
    Poly3.eval_pow, Poly3.eval_varP, Poly3.eval_varT, Poly3.eval_const]
  ring_nf

def poly_1010010101 : Poly3.Poly :=
  ((3 : ℚ) • (pPoly ^ 2)) + ((-5 : ℚ) • pPoly) + ((1 : ℚ) • tPoly) +
    (((3 : ℚ) / 2) • (1 : Poly3.Poly))

theorem certPoly_1010010101_eq (p t : ℝ) :
    Poly3.eval p t 0 (certPoly cert_1010010101) = Poly3.eval p t 0 poly_1010010101 := by
  simp [words7_eq_explicit, poly_1010010101, cert_1010010101, certPoly, rowRhsPoly,
    shortMargPoly, dist7Poly, pPoly, tPoly, Poly3.eval_add, Poly3.eval_sub, Poly3.eval_mul,
    Poly3.eval_smul, Poly3.eval_pow, Poly3.eval_varP, Poly3.eval_varT, Poly3.eval_const]
  ring_nf

def poly_00100 : Poly3.Poly :=
  poly_001001

theorem certPoly_00100_eq (p t : ℝ) :
    Poly3.eval p t 0 (certPoly cert_00100) = Poly3.eval p t 0 poly_00100 := by
  simp [words7_eq_explicit, poly_00100, poly_001001, cert_00100, certPoly, rowRhsPoly,
    shortMargPoly, dist7Poly, pPoly, tPoly, Poly3.eval_add, Poly3.eval_sub, Poly3.eval_mul,
    Poly3.eval_smul, Poly3.eval_pow, Poly3.eval_varP, Poly3.eval_varT, Poly3.eval_const]
  ring_nf

def poly_1010010100 : Poly3.Poly :=
  poly_0010100101

theorem certPoly_1010010100_eq (p t : ℝ) :
    Poly3.eval p t 0 (certPoly cert_1010010100) = Poly3.eval p t 0 poly_1010010100 := by
  simp [words7_eq_explicit, poly_1010010100, poly_0010100101, cert_1010010100, certPoly,
    rowRhsPoly, shortMargPoly, dist7Poly, pPoly, tPoly, Poly3.eval_add, Poly3.eval_sub,
    Poly3.eval_mul, Poly3.eval_smul, Poly3.eval_pow, Poly3.eval_varP, Poly3.eval_varT,
    Poly3.eval_const]
  ring_nf

def poly_00100100 : Poly3.Poly :=
  (pPoly ^ 2) + ((-8 : ℚ) • pPoly) + ((2 : ℚ) • tPoly) + ((3 : ℚ) • (1 : Poly3.Poly))

theorem certPoly_00100100_eq (p t : ℝ) :
    Poly3.eval p t 0 (certPoly cert_00100100) = Poly3.eval p t 0 poly_00100100 := by
  simp [words7_eq_explicit, poly_00100100, cert_00100100, certPoly, rowRhsPoly, shortMargPoly,
    dist7Poly, pPoly, tPoly, Poly3.eval_add, Poly3.eval_sub, Poly3.eval_mul, Poly3.eval_smul,
    Poly3.eval_pow, Poly3.eval_varP, Poly3.eval_varT, Poly3.eval_const]
  ring_nf

def poly_0010100 : Poly3.Poly :=
  ((-2 : ℚ) • (pPoly ^ 2)) + ((-7 : ℚ) • pPoly) + ((3 : ℚ) • tPoly) +
    ((3 : ℚ) • (1 : Poly3.Poly))

theorem certPoly_0010100_eq (p t : ℝ) :
    Poly3.eval p t 0 (certPoly cert_0010100) = Poly3.eval p t 0 poly_0010100 := by
  simp [words7_eq_explicit, poly_0010100, cert_0010100, certPoly, rowRhsPoly, shortMargPoly,
    dist7Poly, pPoly, tPoly, Poly3.eval_add, Poly3.eval_sub, Poly3.eval_mul, Poly3.eval_smul,
    Poly3.eval_pow, Poly3.eval_varP, Poly3.eval_varT, Poly3.eval_const]
  ring_nf

def poly_0010010100 : Poly3.Poly :=
  ((2 : ℚ) • (pPoly ^ 2)) + ((-2 : ℚ) • pPoly) + (((1 : ℚ) / 2) • (1 : Poly3.Poly))

theorem certPoly_0010010100_eq (p t : ℝ) :
    Poly3.eval p t 0 (certPoly cert_0010010100) = Poly3.eval p t 0 poly_0010010100 := by
  simp [words7_eq_explicit, poly_0010010100, cert_0010010100, certPoly, rowRhsPoly,
    shortMargPoly, dist7Poly, pPoly, tPoly, Poly3.eval_add, Poly3.eval_sub, Poly3.eval_mul,
    Poly3.eval_smul, Poly3.eval_pow, Poly3.eval_varP, Poly3.eval_varT, Poly3.eval_const]
  ring_nf

def poly_0010010100100 : Poly3.Poly :=
  ((-8 : ℚ) • (pPoly ^ 3)) + ((-10 : ℚ) • (pPoly ^ 2)) + ((9 : ℚ) • (pPoly * tPoly)) +
    ((9 : ℚ) • pPoly) + ((-3 : ℚ) • tPoly) + (((-3 : ℚ) / 2) • (1 : Poly3.Poly))

theorem certPoly_0010010100100_eq (p t : ℝ) :
    Poly3.eval p t 0 (certPoly cert_0010010100100) = Poly3.eval p t 0 poly_0010010100100 := by
  simp [words7_eq_explicit, poly_0010010100100, cert_0010010100100, certPoly, rowRhsPoly,
    shortMargPoly, dist7Poly, pPoly, tPoly, Poly3.eval_add, Poly3.eval_sub, Poly3.eval_mul,
    Poly3.eval_smul, Poly3.eval_pow, Poly3.eval_varP, Poly3.eval_varT, Poly3.eval_const]
  ring_nf

def poly_00 : Poly3.Poly :=
  poly_100

theorem certPoly_00_eq (p t : ℝ) :
    Poly3.eval p t 0 (certPoly cert_00) = Poly3.eval p t 0 poly_00 := by
  simp [words7_eq_explicit, poly_00, poly_100, cert_00, certPoly, rowRhsPoly, shortMargPoly,
    dist7Poly, pPoly, tPoly, Poly3.eval_add, Poly3.eval_sub, Poly3.eval_mul, Poly3.eval_smul,
    Poly3.eval_pow, Poly3.eval_varP, Poly3.eval_varT, Poly3.eval_const]
  ring_nf

end Step2Sparse

end

end Model

end K5Bridge

end FiniteDependence.MIS
