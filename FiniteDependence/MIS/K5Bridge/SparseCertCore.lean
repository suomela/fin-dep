import FiniteDependence.MIS.K5Bridge.StepLemmas

namespace FiniteDependence.MIS

namespace K5Bridge

namespace Model

open K5Data

set_option maxRecDepth 1000000
set_option maxHeartbeats 20000000

/-!
Core data for the fixed length-14 sparse certificate system used in the streamlined `k = 5`
argument.
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
  set_option maxRecDepth 1000000 in
    decide

theorem words14_length : words14.length = 86 := by
  decide

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

end

end Model

end K5Bridge

end FiniteDependence.MIS
