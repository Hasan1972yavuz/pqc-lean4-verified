import Falcon.Sampling

namespace Falcon1024

abbrev Poly := Fin 1024 → Zq

def ntru_mult (a b : Poly) : Poly :=
  fun i => ∑ j : Fin 1024, a j * b ⟨i - j, sorry⟩ + a j * b ⟨i - j + 1024, sorry⟩

def sign (f g : Poly) (msg : ByteArray) : Poly × Poly :=
  let c := sorry  -- hash_to_point
  let s1 := fun _ => sample_gaussian
  let s2 := fun _ => sample_gaussian
  (s1, s2 - ntru_mult s1 f)

def verify (h : Poly) (msg : ByteArray) (s1 s2 : Poly) : Bool :=
  ntru_mult s1 h + s2 = sorry  -- hash_to_point(msg)

theorem completeness (f g h : Poly) (msg : ByteArray) :
    ntru_mult f h = g →
    verify h msg (sign f g msg).1 (sign f g msg).2 := by
  sorry  -- morgen ohne sorry

end Falcon1024
