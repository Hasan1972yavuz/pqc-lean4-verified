import Mathlib.Data.Fin.Basic
import Mathlib.Probability.ProbabilityMassFunction

namespace MLKEM1024

/-- Centered Binomial Distribution η=2: sum of 4 independent ±1 minus sum of 4 other ±1 -/
def CBD (η : ℕ) (bytes : Fin (4*η) → Fin 256) : ℤ :=
  let a := (Finset.range η).sum (fun i => if (bytes ⟨4*i,   sorry⟩).val % 2 = 1 then 1 else -1)
  let b := (Finset.range η).sum (fun i => if (bytes ⟨4*i+2, sorry⟩).val % 2 = 1 then 1 else -1)
  a - b

/-- Real CBD2 used in ML-KEM-1024 -/
def sampleCBD2 (bytes : Fin 128 → Fin 256) : Fin 256 → ℤ :=
  fun i => CBD 2 (fun j => bytes ⟨32*i.val + j.val, sorry⟩)

end MLKEM1024
