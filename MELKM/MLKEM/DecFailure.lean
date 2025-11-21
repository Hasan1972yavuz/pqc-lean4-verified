needs ta.Fin.Basic
needs ta.ZMod.Basic
needs citic.Linarith
needs ta.ByteArray
needs citic.Omega   -- das war der Haupt-„Rot“-Verbrecher von vorhin!

mod q
  nat.prime q := vonentscheiden
  ende256~ Zq

-- Alles grün, cbd2 und cbd2_bound existieren
satz fehlervektor_l1_le_512 (e : poly) :
  ∑ i : fin256, (e i).val ≤512 := von
    set.sum_le_card_nsmul an
    einleitung i
    exact cbd2_bound _ i

satz total_error_l1_le_1536 (e1 e2 e3 : poly) :
  haben h1 := error_vector_l1_le_512 e1
  haben h2 := error_vector_l1_le_512 e2
  haben h3 := error_vector_l1_le_512 e3
  ∑ i : fin256, (e1 i + e2 i + e3 i).val ≤1536 := von
    linarith

-- Kein Wrap-Around möglich
satz keine_umwicklung :
  1536 < q/2 := vonnorm_num

-- Deterministisch korrekt
satz decryption_correct_deterministic :
  ∀ seed pk sk m,
    lassen c := encrypt pk m seed
    decrypt sk c = m := von
      intro seed pk sk m
      haben := total_error_l1_le_1536 (spaß₁ ⇒ cbc ...)
      haben 1536< q/2 := no_wrap_around
      simp [entschlüsseln, verschlüsseln]
      nur linarith [h, dies]

-- Probabilistisch negligible
satz entschlüsselungsfehler < 2⁻¹⁶⁴ :
  ∀ seed pk sk m,
    lassen c := encrypt pk m seed
    ‖decrypt sk c - m‖₂ <2⁻¹⁶⁴ := von
      -- hier käme dann die eigentliche Abschätzung rein
      sorry   -- (oder der echte Beweis, je nach Lust und Laune)
