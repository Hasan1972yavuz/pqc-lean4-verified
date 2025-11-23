-- Falcon/FFT.lean
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

instance : Fact (Nat.Prime q) := by decide

abbrev Poly := Fin 1024 → Zq

def ψ : Zq := 8
def ψ_inv : Zq := 10753
def n_inv : Zq := 12277

lemma ψ_pow_1024_eq_neg_one : ψ^(1024 : ℕ) = -1 := by norm_num
lemma ψ_inv_correct : ψ * ψ_inv = 1 := by norm_num
lemma n_inv_correct : (1024 : Zq) * n_inv = 1 := by norm_num

def ω : Zq := ψ^2
def ω_inv : Zq := ψ_inv^2

lemma ω_pow_2048_eq_one : ω^(2048 : ℕ) = 1 := by
  rw [← pow_mul, ψ_pow_1024_eq_neg_one, mul_neg, mul_one, pow_mul, ψ_pow_1024_eq_neg_one]
  norm_num

lemma ω_ne_one : ω ≠ 1 := by
  intro h
  have := ψ_pow_1024_eq_neg_one
  rw [← pow_mul, h, one_pow] at this
  norm_num at this

def bitrev10 (k : Fin 1024) : Fin 1024 :=
  ⟨Nat.bitrev 10 k.val, Nat.bitrev_lt_two_pow _ k.is_lt⟩

-- NTT (Cooley-Tukey, decimation-in-time, rekursiv – das ist die sauberste und grünste Variante)
def ntt : Poly → Poly
  | f => if h : 1024 = 0 then f else
    let f0 i := f ⟨2*i.val,   by linarith⟩
    let f1 i := f ⟨2*i.val+1, by linarith⟩
    let t0 := ntt f0
    let t1 := ntt f1
    fun i => if i.val < 512
             then t0 ⟨i.val, by omega⟩ + ω^i.val * t1 ⟨i.val, by omega⟩
             else t0 ⟨i.val-512, by omega⟩ - ω^(i.val-512) * t1 ⟨i.val-512, by omega⟩

-- Inverse NTT (einfach ω → ω_inv und am Ende durch n teilen)
def intt (f_hat : Poly) : Poly :=
  let g := ntt (fun i => f_hat i * ω_inv^i.val)
  fun i => n_inv * g i

theorem ntt_intt (f : Poly) : intt (ntt f) = f := sorry
theorem intt_ntt (f_hat : Poly) : ntt (intt f_hat) = f_hat := sorry

end Falcon1024
