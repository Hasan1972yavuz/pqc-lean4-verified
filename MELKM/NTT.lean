import Mathlib.Data.Fintype.Basic
import Mathlib.Data.ZMod.Basic
import Mathlib.Data.Fin.Basic

namespace MLKEM1024

def q : ℕ := 3329
abbrev Zq := ZMod q

instance : Fact (Nat.Prime q) := sorry_admit   -- später natively

abbrev Poly := Fin 256 → Zq

-- Die 7 Schichten ζ-Werte aus der Kyber-Spec (Table 4)
def ζs : List Zq := [17, 299, 2755, 2021, 1797, 354, 1073]

-- Bit-reversal permutation für n=256
def bitrev (i : Fin 256) : Fin 256 :=
  ⟨Nat.reverseBits i.val 8, by sorry⟩

-- Das ist nur der Rahmen – morgen kommt die echte NTT + INTT + Beweis

end MLKEM1024
