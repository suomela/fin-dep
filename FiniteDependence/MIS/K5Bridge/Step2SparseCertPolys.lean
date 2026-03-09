import FiniteDependence.MIS.K5Bridge.SparseCertStep2Data
import FiniteDependence.MIS.K5Bridge.Step3SparseCore

namespace FiniteDependence.MIS

namespace K5Bridge

namespace Model

noncomputable section

namespace Step2Sparse

open Step3

def poly_1 : Poly3.Poly :=
  pPoly

theorem certPoly_1_eq : certPoly cert_1 = poly_1 := by
  with_unfolding_all decide

def poly_0010100101 : Poly3.Poly :=
  ((-4 : ℚ) • (pPoly ^ 2)) + ((-5 : ℚ) • pPoly) + ((3 : ℚ) • tPoly) +
    (((5 : ℚ) / 2) • (1 : Poly3.Poly))

theorem certPoly_0010100101_eq : certPoly cert_0010100101 = poly_0010100101 := by
  with_unfolding_all decide

def poly_100 : Poly3.Poly :=
  ((-2 : ℚ) • pPoly) + ((1 : ℚ) • (1 : Poly3.Poly))

theorem certPoly_100_eq : certPoly cert_100 = poly_100 := by
  with_unfolding_all decide

def poly_10100101 : Poly3.Poly :=
  ((-1 : ℚ) • (pPoly ^ 2)) + ((-10 : ℚ) • pPoly) + ((4 : ℚ) • tPoly) +
    ((4 : ℚ) • (1 : Poly3.Poly))

theorem certPoly_10100101_eq : certPoly cert_10100101 = poly_10100101 := by
  with_unfolding_all decide

def poly_10100 : Poly3.Poly :=
  ((-1 : ℚ) • (pPoly ^ 2)) + ((-2 : ℚ) • pPoly) + tPoly + ((1 : ℚ) • (1 : Poly3.Poly))

theorem certPoly_10100_eq : certPoly cert_10100 = poly_10100 := by
  with_unfolding_all decide

def poly_001001 : Poly3.Poly :=
  (pPoly ^ 2) + ((-1 : ℚ) • tPoly)

theorem certPoly_001001_eq : certPoly cert_001001 = poly_001001 := by
  with_unfolding_all decide

def poly_100101 : Poly3.Poly :=
  poly_10100

theorem certPoly_100101_eq : certPoly cert_100101 = poly_100101 := by
  with_unfolding_all decide

def poly_100100 : Poly3.Poly :=
  poly_001001

theorem certPoly_100100_eq : certPoly cert_100100 = poly_100100 := by
  with_unfolding_all decide

def poly_00101 : Poly3.Poly :=
  poly_10100

theorem certPoly_00101_eq : certPoly cert_00101 = poly_00101 := by
  with_unfolding_all decide

def poly_101 : Poly3.Poly :=
  ((3 : ℚ) • pPoly) + ((-1 : ℚ) • (1 : Poly3.Poly))

theorem certPoly_101_eq : certPoly cert_101 = poly_101 := by
  with_unfolding_all decide

def poly_1010010101 : Poly3.Poly :=
  ((3 : ℚ) • (pPoly ^ 2)) + ((-5 : ℚ) • pPoly) + ((1 : ℚ) • tPoly) +
    (((3 : ℚ) / 2) • (1 : Poly3.Poly))

theorem certPoly_1010010101_eq : certPoly cert_1010010101 = poly_1010010101 := by
  with_unfolding_all decide

def poly_00100 : Poly3.Poly :=
  poly_001001

theorem certPoly_00100_eq : certPoly cert_00100 = poly_00100 := by
  with_unfolding_all decide

def poly_1010010100 : Poly3.Poly :=
  poly_0010100101

theorem certPoly_1010010100_eq : certPoly cert_1010010100 = poly_1010010100 := by
  set_option maxRecDepth 1000000 in
    with_unfolding_all decide

def poly_00100100 : Poly3.Poly :=
  (pPoly ^ 2) + ((-8 : ℚ) • pPoly) + ((2 : ℚ) • tPoly) + ((3 : ℚ) • (1 : Poly3.Poly))

theorem certPoly_00100100_eq : certPoly cert_00100100 = poly_00100100 := by
  with_unfolding_all decide

def poly_0010100 : Poly3.Poly :=
  ((-2 : ℚ) • (pPoly ^ 2)) + ((-7 : ℚ) • pPoly) + ((3 : ℚ) • tPoly) +
    ((3 : ℚ) • (1 : Poly3.Poly))

theorem certPoly_0010100_eq : certPoly cert_0010100 = poly_0010100 := by
  with_unfolding_all decide

def poly_0010010100 : Poly3.Poly :=
  ((2 : ℚ) • (pPoly ^ 2)) + ((-2 : ℚ) • pPoly) + (((1 : ℚ) / 2) • (1 : Poly3.Poly))

theorem certPoly_0010010100_eq : certPoly cert_0010010100 = poly_0010010100 := by
  with_unfolding_all decide

def poly_0010010100100 : Poly3.Poly :=
  ((-8 : ℚ) • (pPoly ^ 3)) + ((-10 : ℚ) • (pPoly ^ 2)) + ((9 : ℚ) • (pPoly * tPoly)) +
    ((9 : ℚ) • pPoly) + ((-3 : ℚ) • tPoly) + (((-3 : ℚ) / 2) • (1 : Poly3.Poly))

theorem certPoly_0010010100100_eq : certPoly cert_0010010100100 = poly_0010010100100 := by
  with_unfolding_all decide

def poly_00 : Poly3.Poly :=
  poly_100

theorem certPoly_00_eq : certPoly cert_00 = poly_00 := by
  with_unfolding_all decide

end Step2Sparse

end

end Model

end K5Bridge

end FiniteDependence.MIS
