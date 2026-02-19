import FiniteDependence.MIS.K5Bridge.StepLemmas

namespace FiniteDependence.MIS

namespace K5Bridge

namespace Model

open K5Data

/-!
Sparse dual-certificate data for the streamlined `k = 5` Step-3 argument.

The fixed length-14 row system has:
- 1 normalization row,
- 65 stationarity rows at length 13,
- 214 split rows (`m+n=9`, gap 5, with `m,n ∈ {2,…,7}`),
for a total of 280 rows and 86 length-14 unknown cylinders.

This file stores the sparse certificates used in the manuscript/script and provides
computable checkers for `Aᵀ λ = c_prefix`.
-/

noncomputable section

def words14 : List String :=
  (K5Data.allowedWords 14).toList

def words13 : List String :=
  (K5Data.allowedWords 13).toList

inductive RowKind where
  | norm
  | stat13 (u : String)
  | split (m : Nat) (x : String) (n : Nat) (y : String)
deriving DecidableEq, Repr

def splitRows : List RowKind := do
  let dm ← List.range 6
  let m := dm + 2
  let n := 9 - m
  let x ← (K5Data.allowedWords m).toList
  let y ← (K5Data.allowedWords n).toList
  pure (RowKind.split m x n y)

def allRows : List RowKind :=
  RowKind.norm :: (words13.map RowKind.stat13) ++ splitRows

theorem allRows_length : allRows.length = 280 := by
  native_decide

theorem words14_length : words14.length = 86 := by
  native_decide

def rowCoeff (r : RowKind) (w : String) : ℚ :=
  match r with
  | .norm => 1
  | .stat13 u =>
      (if prefixOf w 13 = u then (1 : ℚ) else 0) -
        (if suffixFrom w 1 = u then (1 : ℚ) else 0)
  | .split m x _n y =>
      if prefixOf w m = x ∧ suffixFrom w (m + 5) = y then (1 : ℚ) else 0

def targetCoeff (pref w : String) : ℚ :=
  if prefixOf w pref.length = pref then (1 : ℚ) else 0

def certCoeffAt (cert : List (Nat × ℚ)) (w : String) : ℚ :=
  cert.foldl
    (fun acc rc =>
      let i := rc.1
      let c := rc.2
      acc + c * rowCoeff (allRows.getD i RowKind.norm) w)
    0

def certificateMatches (pref : String) (cert : List (Nat × ℚ)) : Bool :=
  words14.all (fun w => decide (certCoeffAt cert w = targetCoeff pref w))

-- generated cert definitions
def cert_100100101 : List (Nat × ℚ) :=
  [
    (4, (-1 : ℚ)),
    (9, (1 : ℚ)),
    (10, (1 : ℚ)),
    (11, (1 : ℚ)),
    (73, (1 : ℚ)),
    (126, (1 : ℚ)),
    (127, (1 : ℚ)),
    (128, (1 : ℚ)),
    (247, (-1 : ℚ)),
    (248, (-1 : ℚ)),
    (249, (-1 : ℚ)),
  ]

def cert_00101001001 : List (Nat × ℚ) :=
  [
    (8, (1 : ℚ) / 2),
    (9, (1 : ℚ) / 2),
    (26, (-1 : ℚ) / 2),
    (37, (1 : ℚ) / 2),
    (43, (1 : ℚ) / 2),
    (57, (-1 : ℚ) / 2),
    (65, (1 : ℚ) / 2),
    (78, (1 : ℚ) / 2),
    (182, (1 : ℚ) / 2),
    (226, (-1 : ℚ) / 2),
  ]

def cert_100100 : List (Nat × ℚ) :=
  [
    (229, (1 : ℚ)),
    (230, (1 : ℚ)),
    (266, (1 : ℚ)),
  ]

def cert_10100101001001 : List (Nat × ℚ) :=
  [
    (53, (1 : ℚ)),
    (79, (-1 : ℚ)),
    (150, (1 : ℚ)),
    (222, (1 : ℚ)),
    (253, (-1 : ℚ)),
  ]

def cert_10010010101 : List (Nat × ℚ) :=
  [
    (8, (1 : ℚ) / 2),
    (9, (1 : ℚ) / 2),
    (10, (1 : ℚ) / 2),
    (11, (1 : ℚ)),
    (26, (-1 : ℚ) / 2),
    (41, (1 : ℚ) / 2),
    (43, (1 : ℚ) / 2),
    (57, (-1 : ℚ) / 2),
    (78, (1 : ℚ) / 2),
    (88, (1 : ℚ) / 2),
    (127, (1 : ℚ) / 2),
    (128, (1 : ℚ)),
    (226, (-1 : ℚ) / 2),
    (247, (-1 : ℚ)),
    (248, (-1 : ℚ)),
    (249, (-1 : ℚ) / 2),
  ]

def cert_101001001 : List (Nat × ℚ) :=
  [
    (1, (-1 : ℚ) / 2),
    (2, (-1 : ℚ) / 2),
    (8, (1 : ℚ) / 2),
    (9, (1 : ℚ) / 2),
    (11, (1 : ℚ) / 2),
    (17, (-1 : ℚ) / 2),
    (18, (-1 : ℚ) / 2),
    (19, (-1 : ℚ) / 2),
    (27, (1 : ℚ) / 2),
    (32, (-1 : ℚ) / 2),
    (38, (-1 : ℚ) / 2),
    (43, (1 : ℚ) / 2),
    (45, (1 : ℚ) / 2),
    (50, (1 : ℚ) / 2),
    (51, (1 : ℚ) / 2),
    (52, (1 : ℚ)),
    (59, (-1 : ℚ) / 2),
    (67, (-1 : ℚ) / 2),
    (78, (1 : ℚ) / 2),
    (80, (1 : ℚ) / 2),
    (91, (-1 : ℚ) / 2),
    (247, (-1 : ℚ) / 2),
    (248, (-1 : ℚ) / 2),
    (255, (1 : ℚ) / 2),
    (276, (1 : ℚ) / 2),
  ]

def cert_01010101001001 : List (Nat × ℚ) :=
  [
    (2, (-1 : ℚ) / 2),
    (3, (1 : ℚ) / 2),
    (19, (-1 : ℚ) / 2),
    (32, (-1 : ℚ)),
    (39, (1 : ℚ) / 2),
    (51, (-1 : ℚ) / 2),
    (66, (-1 : ℚ) / 2),
    (67, (-1 : ℚ)),
    (72, (-1 : ℚ) / 2),
    (79, (-1 : ℚ) / 2),
    (91, (-1 : ℚ)),
    (150, (1 : ℚ) / 2),
    (224, (1 : ℚ)),
    (252, (1 : ℚ) / 2),
    (253, (-1 : ℚ) / 2),
    (255, (1 : ℚ) / 2),
  ]

def cert_100100100100 : List (Nat × ℚ) :=
  [
    (8, (-1 : ℚ) / 2),
    (9, (-1 : ℚ) / 2),
    (11, (-1 : ℚ)),
    (26, (1 : ℚ) / 2),
    (43, (-1 : ℚ) / 2),
    (64, (-1 : ℚ) / 2),
    (75, (-1 : ℚ) / 2),
    (78, (-1 : ℚ) / 2),
    (88, (-1 : ℚ) / 2),
    (128, (-1 : ℚ)),
    (173, (1 : ℚ) / 2),
    (206, (1 : ℚ) / 2),
    (229, (1 : ℚ)),
    (247, (1 : ℚ)),
    (248, (1 : ℚ)),
    (249, (1 : ℚ) / 2),
    (253, (1 : ℚ) / 2),
  ]

def cert_01001001 : List (Nat × ℚ) :=
  [
    (253, (1 : ℚ)),
    (254, (1 : ℚ)),
    (255, (1 : ℚ)),
  ]

def cert_100100100 : List (Nat × ℚ) :=
  [
    (16, (1 : ℚ)),
    (32, (1 : ℚ)),
    (38, (1 : ℚ)),
    (66, (1 : ℚ)),
    (67, (1 : ℚ)),
    (85, (1 : ℚ)),
    (91, (1 : ℚ)),
    (124, (1 : ℚ)),
    (224, (-1 : ℚ)),
    (252, (-1 : ℚ)),
  ]

def cert_01001001001 : List (Nat × ℚ) :=
  [
    (16, (1 : ℚ)),
    (32, (1 : ℚ)),
    (39, (-1 : ℚ)),
    (66, (1 : ℚ)),
    (67, (1 : ℚ)),
    (85, (1 : ℚ)),
    (91, (1 : ℚ)),
    (124, (1 : ℚ)),
    (224, (-1 : ℚ)),
    (252, (-1 : ℚ)),
  ]

def cert_10010010010101 : List (Nat × ℚ) :=
  [
    (16, (1 : ℚ)),
    (66, (1 : ℚ)),
    (124, (1 : ℚ)),
    (252, (-1 : ℚ)),
  ]

def cert_001001 : List (Nat × ℚ) :=
  [
    (174, (1 : ℚ)),
    (209, (1 : ℚ)),
    (245, (1 : ℚ)),
  ]

def cert_1010100101 : List (Nat × ℚ) :=
  [
    (11, (-1 : ℚ) / 2),
    (16, (1 : ℚ) / 2),
    (29, (-1 : ℚ) / 2),
    (30, (-1 : ℚ) / 2),
    (32, (1 : ℚ) / 2),
    (55, (-1 : ℚ) / 2),
    (56, (-1 : ℚ) / 2),
    (59, (1 : ℚ) / 2),
    (66, (1 : ℚ) / 2),
    (67, (1 : ℚ) / 2),
    (99, (1 : ℚ) / 2),
    (101, (1 : ℚ) / 2),
    (121, (1 : ℚ) / 2),
    (132, (1 : ℚ) / 2),
    (233, (-1 : ℚ) / 2),
    (252, (-1 : ℚ) / 2),
  ]

def certificatePrefixes : List String :=
  ["100100101", "00101001001", "100100", "10100101001001", "10010010101", "101001001",
    "01010101001001", "100100100100", "01001001", "100100100", "01001001001",
    "10010010010101", "001001"]

def certificates : List (String × List (Nat × ℚ)) :=
  [("100100101", cert_100100101), ("00101001001", cert_00101001001), ("100100", cert_100100),
    ("10100101001001", cert_10100101001001), ("10010010101", cert_10010010101), ("101001001", cert_101001001),
    ("01010101001001", cert_01010101001001), ("100100100100", cert_100100100100), ("01001001", cert_01001001),
    ("100100100", cert_100100100), ("01001001001", cert_01001001001), ("10010010010101", cert_10010010010101),
    ("001001", cert_001001)]

theorem certificate_count : certificates.length = 13 := by
  native_decide

def supportSizes : List Nat :=
  certificates.map (fun p => p.2.length)

theorem support_sizes_sorted :
    supportSizes.insertionSort (fun a b => a ≤ b) = [3, 3, 3, 4, 5, 10, 10, 10, 11, 16, 16, 17, 25] := by
  native_decide

theorem support_sizes_total : supportSizes.foldl (· + ·) 0 = 133 := by
  native_decide

theorem support_sizes_max : supportSizes.foldl max 0 = 25 := by
  native_decide

theorem row_index_profile :
    let idxs := List.flatMap (fun p => p.2.map (fun rc => rc.1)) certificates
    let uniq := (List.eraseDups idxs).insertionSort (· ≤ ·)
    (idxs.length = 133) ∧ (uniq.length = 65) := by
  native_decide

theorem certificates_match_targets :
    certificates.all (fun p => certificateMatches p.1 p.2) = true := by
  native_decide

theorem cert_1010100101_matches :
    certificateMatches "1010100101" cert_1010100101 = true := by
  native_decide

end

end Model

end K5Bridge

end FiniteDependence.MIS
