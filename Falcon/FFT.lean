-- Datei: Falcon/FFT.lean
import Mathlib.Data.Fin.Basic
import Mathlib.Data.ZMod.Basic
import Mathlib.Tactic.NormNum
import Mathlib.Algebra.BigOperators.Pi
import Mathlib.Algebra.Module.Pi

namespace Falcon1024

def q : ℕ := 12289
abbrev Zq := ZMod q

example : Fact (Nat.Prime q) := by norm_num   -- grün, q ist wirklich prim

abbrev Poly := Fin 1024 → Zq

def ψ : Zq := 8
def ψ_inv : Zq := 10753
def n_inv : Zq := 12277

lemma ψ_pow_1024_eq_neg_one : ψ^(1024:Zq) = -1 := by norm_num
lemma ψ_inv_correct : ψ * ψ_inv = 1 := by norm_num
lemma n_inv_correct : (1024 : Zq) * n_inv = 1 := by norm_num

/-- Primitive 2048-te Einheitswurzel (da 1024-te = -1) — für NTT-Basis —/
def ω : Zq := ψ^2   -- ψ² ist primitive 2048-te Wurzel
def ω_inv : Zq := ψ_inv^2

lemma ω_pow_2048_eq_one : ω^(2048:Zq) = 1 := by
  rw [← pow_mul, ← ψ_pow_1024_eq_neg_one, mul_comm, pow_mul]
  norm_num

lemma ω_ne_one : ω ≠ 1 := by
  intro h
  have : ω^1024 = -1 := by
    rw [← pow_mul, h, one_pow]
  norm_num at this

/-- Bit-reversal Permutation —/
def bitrev (k : Fin 1024) : Fin 1024 :=
  ⟨Nat.reverseBits k.val 10, by
    have := Nat.reverseBits_lt (by decide) k.is_lt
    exact this⟩

/-- Number-Theoretic Transform (Gentleman-Sande, decimation-in-frequency) —/
def ntt (f : Poly) : Poly := fun k =>
  let m := 1 <<< (10 - k.val.reverseBits 10).trailingZeros
  let mut a := f (bitrev k)
  for i in [0:m], do
    let tw := ω^(bitrev ⟨i, by omega⟩ * (1024/m))
    let t := tw * a
    let u := a
    a := u + t
    if i % 2 = 1 then a := a * n_inv
  a

/-- Inverse NTT —/
def intt (f_hat : Poly) : Poly := ntt (fun i => f_hat i * n_inv)

/-- Korrektheit der NTT/INTT für Falcon-1024 —/
theorem ntt_intt_id (f : Poly) : intt (ntt f) = f := sorry   -- hier kommt später der echte Beweis
theorem intt_ntt_id (f_hat : Poly) : ntt (intt f_hat) = f_hat := sorry

end Falcon1024
