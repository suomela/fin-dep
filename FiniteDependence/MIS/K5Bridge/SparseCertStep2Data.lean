import FiniteDependence.MIS.K5Bridge.SparseCertData

namespace FiniteDependence.MIS

namespace K5Bridge

namespace Model

namespace Step2Sparse

/-!
Sparse dual-certificate data for Step-2 marginals used by the 7-row/4-row
split-cancellation identities in the streamlined `k = 5` proof.

All certificates are over the same length-14 fixed system as `SparseCertData`.
-/

def cert_1 : List (Nat × ℚ) :=
  [ (96, 1), (98, 1), (122, 1), (131, 1), (194, 1), (199, 1), (204, 1), (205, 1),
    (206, 1), (266, 1), (269, 1), (272, 1) ]

def cert_0010100101 : List (Nat × ℚ) :=
  [ (8, -1 / 2), (9, -1 / 2), (21, -1 / 2), (28, -1 / 2), (43, -1 / 2), (53, -1 / 2),
    (58, 1 / 2), (73, -1 / 2), (153, 1 / 2), (247, 1), (248, 1), (249, 1 / 2), (276, -1 / 2) ]

def cert_100 : List (Nat × ℚ) :=
  [ (122, 1), (162, 1), (194, 1), (266, 1), (269, 1) ]

def cert_10100101 : List (Nat × ℚ) :=
  [ (12, 1), (16, 1), (24, -1), (48, -1), (76, -1), (97, 1), (99, 1), (101, 1), (130, 1),
    (247, 1), (252, -1), (275, -1), (276, -1) ]

def cert_10100 : List (Nat × ℚ) :=
  [ (199, 1), (237, 1), (272, 1) ]

def cert_001001 : List (Nat × ℚ) :=
  [ (174, 1), (209, 1), (245, 1) ]

def cert_100101 : List (Nat × ℚ) :=
  [ (233, 1), (234, 1), (269, 1) ]

def cert_100100 : List (Nat × ℚ) :=
  [ (229, 1), (230, 1), (266, 1) ]

def cert_00101 : List (Nat × ℚ) :=
  [ (179, 1), (213, 1), (248, 1), (251, 1) ]

def cert_101 : List (Nat × ℚ) :=
  [ (199, 1), (204, 1), (205, 1), (206, 1), (237, 1), (241, 1), (272, 1) ]

def cert_1010010101 : List (Nat × ℚ) :=
  [ (7, -1 / 2), (24, -1 / 2), (25, -1 / 2), (48, -1 / 2), (56, 1 / 2), (78, -1 / 2),
    (122, 1 / 2), (198, 1), (221, 1 / 2), (229, -1 / 2), (258, 1 / 2) ]

def cert_00100 : List (Nat × ℚ) :=
  [ (174, 1), (209, 1), (245, 1) ]

def cert_1010010100 : List (Nat × ℚ) :=
  [ (4, -1 / 2), (8, -1 / 2), (9, -1 / 2), (11, -1 / 2), (21, -1 / 2), (28, 1 / 2),
    (32, 1 / 2), (43, -1 / 2), (45, -1 / 2), (53, 1 / 2), (54, 1), (59, 1 / 2), (67, 1 / 2),
    (80, -1 / 2), (91, 1 / 2), (223, 1 / 2), (230, -1 / 2), (247, 1 / 2), (248, 1 / 2),
    (249, 1 / 2) ]

def cert_00100100 : List (Nat × ℚ) :=
  [ (66, 1), (67, 1), (68, 1), (69, 1), (70, 1), (71, 1), (72, 1), (250, -1), (251, -1),
    (252, -1) ]

def cert_0010100 : List (Nat × ℚ) :=
  [ (247, 1), (248, 1), (249, 1) ]

def cert_0010010100 : List (Nat × ℚ) :=
  [ (4, 1 / 2), (5, 1 / 2), (19, 1 / 2), (27, 1 / 2), (40, 1 / 2), (51, 1 / 2), (52, 1 / 2),
    (74, 1 / 2), (137, -1 / 2), (176, 1 / 2), (207, 1 / 2) ]

def cert_0010010100100 : List (Nat × ℚ) :=
  [ (8, -1 / 2), (9, -1 / 2), (21, -1 / 2), (43, -1 / 2), (53, -1 / 2), (73, 1 / 2),
    (75, -1 / 2), (79, 1 / 2), (150, -1 / 2), (173, 1 / 2), (222, -1 / 2), (249, 1 / 2),
    (253, 1 / 2) ]

def cert_00 : List (Nat × ℚ) :=
  [ (104, 1), (141, 1), (174, 1), (179, 1), (245, 1), (248, 1), (251, 1) ]

theorem cert_1_matches : certificateMatches "1" cert_1 = true := by native_decide
theorem cert_0010100101_matches : certificateMatches "0010100101" cert_0010100101 = true := by native_decide
theorem cert_100_matches : certificateMatches "100" cert_100 = true := by native_decide
theorem cert_10100101_matches : certificateMatches "10100101" cert_10100101 = true := by native_decide
theorem cert_10100_matches : certificateMatches "10100" cert_10100 = true := by native_decide
theorem cert_001001_matches : certificateMatches "001001" cert_001001 = true := by native_decide
theorem cert_100101_matches : certificateMatches "100101" cert_100101 = true := by native_decide
theorem cert_100100_matches : certificateMatches "100100" cert_100100 = true := by native_decide
theorem cert_00101_matches : certificateMatches "00101" cert_00101 = true := by native_decide
theorem cert_101_matches : certificateMatches "101" cert_101 = true := by native_decide
theorem cert_1010010101_matches : certificateMatches "1010010101" cert_1010010101 = true := by native_decide
theorem cert_00100_matches : certificateMatches "00100" cert_00100 = true := by native_decide
theorem cert_1010010100_matches : certificateMatches "1010010100" cert_1010010100 = true := by native_decide
theorem cert_00100100_matches : certificateMatches "00100100" cert_00100100 = true := by native_decide
theorem cert_0010100_matches : certificateMatches "0010100" cert_0010100 = true := by native_decide
theorem cert_0010010100_matches : certificateMatches "0010010100" cert_0010010100 = true := by native_decide
theorem cert_0010010100100_matches : certificateMatches "0010010100100" cert_0010010100100 = true := by native_decide
theorem cert_00_matches : certificateMatches "00" cert_00 = true := by native_decide

end Step2Sparse

end Model

end K5Bridge

end FiniteDependence.MIS
