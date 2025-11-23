-- Datei: Falcon/FFT.lean
import Mathlib.Data.Fin.Basic
import Mathlib.Data.ZMod.Basic
import Mathlib.Tactic.NormNum
import Mathlib.Algebra.BigOperators.Pi
import Mathlib.Algebra.Module.Pi
import Mathlib.Data.Nat.Pow
import Mathlib.Data.Nat.Bitwise

open BigOperators

namespace Falcon1024

def q : ℕ := 12289
abbrev Zq := ZMod q

-- q ist wirklich prim (wichtig für ZMod)
instance : Fact (Nat.Prime q) := by decide

abbrev Poly := Fin 1024 → Zq

def ψ : Zq := 8
def ψ_inv : Zq := 10753
def n_inv : Zq := 12277   -- 1024⁻¹ mod q

lemma ψ_pow_1024_eq_neg_one : ψ^(1024 : ℕ) = -1 := by norm_num
lemma ψ_inv_correct : ψ * ψ_inv = 1 := by norm_num
lemma n_inv_correct : (1024 : Zq) * n_inv = 1 := by norm_num

def ω : Zq := ψ^2
def ω_inv : Zq := ψ_inv^2

lemma ω_is_primitive_2048th_root : ω^(2048 : ℕ) = 1 ∧ ω^(1024 : ℕ) ≠ 1 := by
  constructor
  · rw [pow_mul, ψ_pow_1024_eq_neg_one, mul_neg, mul_one, pow_mul, ψ_pow_1024_eq_neg_one]
    norm_num
  · intro h
    have : ψ^(1024 : ℕ) = 1 := by rw [← pow_mul, h, one_pow]; norm_num
    norm_num at this

-- Bit-reversal für 10 Bit (1024 = 2^10)
def bitrev10 (k : Fin 1024) : Fin 1024 :=
  ⟨Nat.bitrev 10 k.val, by
    rw [Nat.bitrev_lt_two_pow]
    exact k.is_lt⟩

-- NTT (Gentleman-Sande butterfly, decimation-in-frequency)
def ntt (f : Poly) : Poly := fun k =>
  let mut a := f (bitrev10 k)
  let logm := (10 - (k.val.bitrev 10).trailingZeros)
  for i in [0:2^logm], do
    let m := 1 <<< logm
    let tw := ω^((bitrev10 ⟨i, by omega⟩).val * (1024 / (2*m)))
    let t := tw * a
    a := if i % 2 = 0 then a + t else a - t
  if logm < 10 then a * n_inv else a

-- Inverse NTT (einfach mit ω_inv und Faktor n_inv am Ende)
def intt (f_hat : Poly) : Poly :=
  let g := ntt (fun i => f_hat i * ω_inv^(bitrev10 i).val)
  fun i => g i * n_inv

-- Korrektheit (fürs Erste sorry – wird später geschlossen)
theorem ntt_intt (f : Poly) : intt (ntt f) = f := sorry
theorem intt_ntt (f_hat : Poly) : ntt (intt f_hat) = f_hat := sorry

end Falcon1024
