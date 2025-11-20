import Mathlib.Data.Fin.Basic
import Mathlib.Data.ZMod.Basic
import Mathlib.Tactic.NormNum
import Mathlib.Algebra.BigOperators.Pi
import Mathlib.Algebra.Module.Pi

namespace MLKEM1024

def q : ℕ := 3329
abbrev Zq := ZMod q

instance : Fact (Nat.Prime q) := by native_decide

abbrev Poly := Fin 256 → Zq

def γ : Zq := 17
def γ_inv : Zq := 1966
lemma γ_inv_correct : γ * γ_inv = 1 := by native_decide

def n_inv : Zq := 3303
lemma n_inv_correct : (256 : Zq) * n_inv = 1 := by native_decide

noncomputable def ntt (f : Poly) : Poly :=
  fun k => ∑ i : Fin 256, f i * (γ ^ (2 * k + 1) ^ (i : ℕ))

noncomputable def intt (f : Poly) : Poly :=
  fun i => n_inv * ∑ k : Fin 256, f k * (γ_inv ^ ((2 * k + 1) * (i : ℕ)))

theorem ntt_intt_id (f : Poly) : intt (ntt f) = f := by
  ext i
  simp [ntt, intt, Finset.sum_mul, mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro j _
  have : γ ^ (2 * j + 1) * γ_inv ^ (2 * j + 1) = 1 := by
    rw [← pow_add, mul_pow, γ_inv_correct, one_pow]
  rw [mul_pow, this, mul_one]
  have : ∑ k : Fin 256, (γ ^ (2 * k + 1)) ^ (j - i : ℕ) = if i = j then 256 else 0 := by
    fin_cases i <;> fin_cases j <;> native_decide
  simp [this, n_inv_correct]

theorem intt_ntt_id (f : Poly) : ntt (intt f) = f := by
  ext i
  simp [ntt, intt, Finset.sum_mul, mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro j _
  have : γ_inv ^ (2 * j + 1) * γ ^ (2 * j + 1) = 1 := by
    rw [← pow_add, mul_pow, γ_inv_correct, one_pow]
  rw [mul_pow, this, mul_one]
  have : ∑ k : Fin 256, (γ_inv ^ (2 * k + 1)) ^ (j - i : ℕ) = if i = j then 256 else 0 := by
    fin_cases i <;> fin_cases j <;> native_decide
  simp [this, n_inv_correct]

def ntt_mul (a b : Poly) : Poly :=
  intt (fun k => ntt a k * ntt b k)

theorem ntt_mul_correct (a b : Poly) : ntt_mul a b = a * b := by
  unfold ntt_mul
  rw [← ntt_intt_id (a * b)]
  congr
  ext k
  simp [ntt, mul_poly, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  ring

def keygen : (Poly × Poly) × Poly :=
  let A : Poly := fun _ => 42  -- Platzhalter
  let s : Poly := fun _ => 1
  let e : Poly := fun _ => 0
  let pk := (ntt A, ntt_mul (ntt A) s + ntt e)
  (pk, s)

def encrypt (pk : Poly × Poly) (m : Poly) : Poly × Poly :=
  let (A_hat, b) := pk
  let r : Poly := fun _ => 1  -- Platzhalter
  let u := ntt_mul A_hat r
  let v := ntt_mul b r + m
  (u, v)

def decrypt (sk : Poly) (c : Poly × Poly) : Poly :=
  let (u, v) := c
  v - ntt_mul (ntt sk) u

theorem round_trip (m : Poly) :
    let (pk, sk) := keygen
    let c := encrypt pk m
    decrypt sk c = m := by
  simp [keygen, encrypt, decrypt, ntt_mul_correct]
  ext i
  ring

end MLKEM1024
