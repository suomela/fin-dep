import Std.Data.TreeMap
import Mathlib

namespace FiniteDependence.MIS

/-!
A small *computable* multivariate polynomial type in three variables over `ℚ`.

We use this to run exact-algebra computations (via `native_decide`) without relying on
Mathlib's (non-executable) polynomial implementations.

The variables are intended to be `p`, `t`, `u` in the k=5 proof search, but this file
is purely algebraic.
-/

namespace Poly3

structure Monom where
  pExp : Nat
  tExp : Nat
  uExp : Nat
deriving DecidableEq, Repr

instance : Ord Monom where
  compare a b :=
    match compare a.pExp b.pExp with
    | .eq =>
        match compare a.tExp b.tExp with
        | .eq => compare a.uExp b.uExp
        | o => o
    | o => o

def Monom.mul (a b : Monom) : Monom :=
  ⟨a.pExp + b.pExp, a.tExp + b.tExp, a.uExp + b.uExp⟩

abbrev Term := Monom × ℚ

def addTermMap (m : Std.TreeMap Monom ℚ) (t : Term) : Std.TreeMap Monom ℚ :=
  let (mono, coeff) := t
  if coeff = 0 then
    m
  else
    match m.get? mono with
    | some c0 =>
        let c1 := c0 + coeff
        if c1 = 0 then m.erase mono else m.insert mono c1
    | none =>
        m.insert mono coeff

def normalize (ts : List Term) : List Term :=
  (ts.foldl addTermMap {}).toList

structure Poly where
  terms : List Term
deriving DecidableEq, Repr

def mk (ts : List Term) : Poly :=
  ⟨normalize ts⟩

def const (q : ℚ) : Poly :=
  if q = 0 then
    ⟨[]⟩
  else
    ⟨[(⟨0, 0, 0⟩, q)]⟩

def varP : Poly := ⟨[(⟨1, 0, 0⟩, 1)]⟩
def varT : Poly := ⟨[(⟨0, 1, 0⟩, 1)]⟩
def varU : Poly := ⟨[(⟨0, 0, 1⟩, 1)]⟩

def add (a b : Poly) : Poly :=
  mk (a.terms ++ b.terms)

def neg (a : Poly) : Poly :=
  mk (a.terms.map (fun (m, c) => (m, -c)))

def sub (a b : Poly) : Poly :=
  add a (neg b)

def smul (q : ℚ) (a : Poly) : Poly :=
  if q = 0 then
    const 0
  else
    mk (a.terms.map (fun (m, c) => (m, q * c)))

def mul (a b : Poly) : Poly :=
  mk <|
    List.flatMap (fun (m1, c1) =>
        b.terms.map (fun (m2, c2) => (Monom.mul m1 m2, c1 * c2)))
      a.terms

def pow (a : Poly) : Nat → Poly
  | 0 => const 1
  | n + 1 => mul (pow a n) a

instance : Zero Poly := ⟨const 0⟩
instance : One Poly := ⟨const 1⟩
instance : Add Poly := ⟨add⟩
instance : Neg Poly := ⟨neg⟩
instance : Sub Poly := ⟨sub⟩
instance : Mul Poly := ⟨mul⟩
instance : Pow Poly Nat := ⟨pow⟩
instance : OfNat Poly n := ⟨const n⟩
instance : SMul ℚ Poly := ⟨smul⟩

end Poly3

end FiniteDependence.MIS
