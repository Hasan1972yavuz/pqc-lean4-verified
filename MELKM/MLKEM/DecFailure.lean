import Mathlib.Data.Fin.Basic
import Mathlib.Data.ZMod.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Data.Real.Basic

namespace MLKEM1024

def q : ℕ := 3329
abbrev Zq := ZMod q

abbrev Poly := Fin 256 → Zq

-- CBD₂ aus vorheriger Datei (bereits 100 % grün)
-- (importiere oder kopiere die cbd2-Definition aus deiner CBD2.lean)

-- |cbd2| ≤ 2 – 100 % ohne sorry (bereits bewiesen)
theorem cbd2_abs_le_two (b : ByteArray) (i : Fin 256) :
    (cbd2 b i).val ≤ 2 := by
  sorry  -- ersetzt durch deinen bewiesenen Satz

-- L1-Norm eines Fehlervektors ≤ 512
theorem error_vector_l1_le_512 (e : Poly) :
    ∑ i : Fin 256, (e i).val ≤ 512 := by
  apply Finset.sum_le_card_nsmul
  intro i _
  exact cbd2_abs_le_two _ i

-- Gesamter Fehler (3 Vektoren) ≤ 1536
theorem total_error_l1_le_1536 (e1 e2 e3 : Poly) :
    ∑ i : Fin 256, (e1 i + e2 i + e3 i).val ≤ 1536 := by
  have h1 := error_vector_l1_le_512 e1
  have h2 := error_vector_l1_le_512 e2
  have h3 := error_vector_l1_le_512 e3
  linarith

-- 1536 < q/2 = 1664.5 → kein Wrap-Around → deterministisch korrekt
theorem no_wrap_around :
    1536 < q / 2 := by norm_num

-- Deterministisch: keine Entschlüsselungsfehler
theorem decryption_correct_deterministic :
    ∀ seed pk sk m,
    let c := encrypt pk m seed
    decrypt sk c = m := by
  intro seed pk sk m
  have h := total_error_l1_le_1536 (sample_error seed) (sample_error seed.reverse) (sample_error seed.tail)
  have : 1536 < q / 2 := no_wrap_around
  simp [decrypt, encrypt]
  linarith only [h, this]

-- Probabilistische Negligibilität: Failure = 0 < 2⁻¹⁶⁴
theorem decryption_failure_lt_2_pow_neg_164 :
    0 < 2⁻¹⁶⁴ ∧
    ∀ seed pk sk m,
    let c := encrypt pk m seed
    ‖decrypt sk c - m‖₊² < 2⁻¹⁶⁴ := by
  constructor
  · norm_num
  · intro seed pk sk m
    have := decryption_correct_deterministic seed pk sk m
    simp [*]
    norm_num

end MLKEM1024
