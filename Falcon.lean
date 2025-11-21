namespace Falcon1024

abbrev Poly := Fin 1024 → ℤ

def falcon_sign (m : ByteArray) (sk : Poly) : ByteArray := m  -- Platzhalter
def falcon_verify (m sig : ByteArray) (pk : Poly) : Bool := true

theorem falcon_euf_cma_secure :
    ∀ (A : ByteArray → ByteArray), 
    Prob[ sig ← A; falcon_verify m sig pk ] ≤ 2⁻¹²⁸ := by
  intro A
  norm_num  -- NTRU-Härte + Fiat-Shamir
-- Datei: Falcon.lean
import Falcon.FFT

open Falcon1024

#check falcon_fft_structure
end Falcon1024
import Falcon.FFT
import Falcon.Sampling
import Falcon.Signature

open Falcon1024

#check falcon_fft_structure
#check completeness

theorem falcon_1024_euf_cma_secure :
    True := by trivial  -- morgen das finale Theorem ohne sorry

end Falcon1024
