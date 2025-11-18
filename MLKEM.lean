import Mathlib.Algebra.BigOperators.Basic
import Mathlib.Data.Finmap
import Mathlib.Data.ZMod.Basic

namespace MLKEM1024

def k := 4
def η1 := 2
def η2 := 2
def du := 10
def dv := 4

def q : ℤ := 3329
instance : Fact (Nat.Prime 3329) := sorry -- wird später bewiesen

def n := 256

abbrev R := Polynomial (ZMod q)
abbrev V := Fin k → R

end MLKEM1024
