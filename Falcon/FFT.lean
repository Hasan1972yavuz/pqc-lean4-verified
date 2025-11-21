-- Datei: Falcon/FFT.lean
import Mathlib.Data.Fin.Basic
import Mathlib.Data.ZMod.Basic
import Mathlib.Tactic.NormNum
import Mathlib.Algebra.BigOperators.Pi
import Mathlib.Algebra.Module.Pi

namespace Falcon1024

def q : ℕ := 12289
abbrev Zq := ZMod q

instance : Fact (Nat.Prime q) := by native_decide

abbrev Poly := Fin 1024 → Zq

def ψ : Zq := 8
def ψ_inv : Zq := 10753
def n_inv : Zq := 12277

lemma ψ_pow_1024_eq_neg_one : ψ ^ 1024 = -1 := by native_decide
lemma ψ_inv_correct : ψ * ψ_inv = 1 := by native_decide
lemma n_inv_correct : (1024 : Zq) * n_inv = 1 := by native_decide

noncomputable def fft (f : Poly) : Poly :=
  fun k => ∑ i : Fin 1024, f i * (ψ ^ (2 * k + 1)) ^ (i : ℕ)

noncomputable def ifft (f : Poly) : Poly :=
  fun i => n_inv * ∑ k : Fin 1024, f k * (ψ_inv ^ ((2 * k + 1) * (i : ℕ)))

theorem fft_ifft_id (f : Poly) : ifft (fft f) = f := by
  ext i
  simp [fft, ifft]
  rw [Finset.mul_sum, Finset.sum_comm]
  have H : ∀ j : Fin 1024, 
      (∑ k : Fin 1024, (ψ ^ (2 * k + 1)) ^ (j : ℕ) * (ψ_inv ^ ((2 * k + 1) * (i : ℕ)))) = 
      if j = i then (1024 : Zq) else 0 := by
    intro j; fin_cases i <;> fin_cases j <;> native_decide
  simp [H, n_inv_correct]

theorem ifft_fft_id (f : Poly) : fft (ifft f) = f := by
  ext i
  simp [fft, ifft]
  rw [Finset.mul_sum, Finset.sum_comm]
  have H : ∀ j : Fin 1024, 
      (∑ k : Fin 1024, (ψ_inv ^ ((2 * k + 1) * (j : ℕ))) * (ψ ^ (2 * k + 1)) ^ (i : ℕ)) = 
      if j = i then (1024 : Zq) else 0 := by
    intro j; fin_cases i <;> fin_cases j <;> native_decide
  simp [H, n_inv_correct]

theorem falcon_fft_structure : ∀ f : Poly, ifft (fft f) = f ∧ fft (ifft f) = f := by
  intro f; exact ⟨fft_ifft_id f, ifft_fft_id f⟩

end Falcon1024
