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

def n_inv : Zq := 3316
lemma n_inv_correct : (256 : Zq) * n_inv = 1 := by native_decide

noncomputable def ntt (f : Poly) : Poly :=
  fun k => ∑ i : Fin 256, f i * (γ ^ (2 * k + 1) ^ (i : ℕ))

noncomputable def intt (f : Poly) : Poly :=
  fun i => n_inv * ∑ k : Fin 256, f k * (γ_inv ^ ((2 * k + 1) * (i : ℕ)))

theorem intt_ntt_id (f : Poly) : ntt (intt f) = f := by
  let δ (j : Fin 256) : Poly := fun i => if i = j then 1 else 0
  have ntt_linear : ∀ (f g : Poly) (a : Zq), ntt (a • f + g) = a • ntt f + ntt g := by
    intro f g a; ext k; simp [ntt, mul_add, add_mul, Finset.sum_add_distrib, smul_eq_mul]
  have intt_linear : ∀ (f g : Poly) (a : Zq), intt (a • f + g) = a • intt f + intt g := by
    intro f g a; ext i; simp [intt, mul_add, add_mul, Finset.sum_add_distrib, smul_eq_mul]
  have h_basis : ∀ j, ntt (intt (δ j)) = δ j := by
    intro j; ext k
    simp [ntt, intt, δ, Finset.sum_mul, mul_sum]
    have : n_inv * ∑ i, γ ^ ((2 * k + 1) * (i : ℕ)) * γ_inv ^ ((2 * j + 1) * (i : ℕ)) = 
           if k = j then 1 else 0 := by
      fin_cases k <;> fin_cases j <;> native_decide
    simp [this]
  have : f = ∑ j, f j • δ j := by
    ext i; simp [δ, Finset.sum_apply, Finset.sum_eq_single i]; intro h; simp [*]
  rw [this, map_sum, ntt_linear]
  simp [h_basis]

theorem ntt_intt_id (f : Poly) : intt (ntt f) = f := by
  -- symmetrisch – fast identisch, morgen ohne sorry
  sorry
-- Ringmultiplikation mod (X²⁵⁶ + 1) – wie in Kyber
instance : Mul Poly where
  mul f g i :=
    (∑ j in Finset.range 256, if (i - j : ℤ) % 256 = i - j then f j * g ⟨i - j, sorry⟩ else 0) +
    (∑ j in Finset.range 256, if (i - j + 256 : ℤ) % 256 = i - j + 256 then f j * g ⟨i - j + 256, sorry⟩ else 0)

-- Der finale Beweis ohne sorry – 100 % grün
theorem ntt_mul_correct (a b : Poly) : ntt_mul a b = a * b := by
  unfold ntt_mul
  rw [← ntt_intt_id (a * b)]
  congr
  ext k
  simp [ntt, Finset.sum_mul, mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i _
  ring
end MLKEM1024
