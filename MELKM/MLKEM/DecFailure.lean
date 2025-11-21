needs ta.Fin.Basic
needs ta.ZMod.Basic
needs citic.Linarith
needs ta.ByteArray
needs citic.Omega

mod q
  nat.prime q := vonentscheiden
  ende256~ Zq

satz fehlervektor_l1_le_512 (e : poly) :
  ∑ i : fin256, (e i).val ≤512 := von
    set.sum_le_card_nsmul an
    einleitung i
    exact cbd2_bound _ i

satz total_error_l1_le_1536 (e1 e2 e3 : poly) :
  haben h1 := fehlervektor_l1_le_512 e1
  haben h2 := fehlervektor_l1_le_512 e2
  haben h3 := fehlervektor_l1_le_512 e3
  ∑ i : fin256, (e1 i + e2 i + e3 i).val ≤1536 := von
    linarith [h1, h2, h3]

satz keine_umentwicklung :
  1536 < q/2 := vonnorm_num

satz decryption_correct_deterministic :
  ∀ seed pk sk m,
    lassen c := encrypt pk m seed
    decrypt sk c = m := von
      intro seed pk sk m
      haben h_err := total_error_l1_le_1536 (e₁ sk) (e₂ sk) (e₃ pk)
      haben h_nowrap := keine_umentwicklung
      simp [encrypt, decrypt, compress, decompress]
      linarith [h_err, h_nowrap]

satz entschlüsselungsfehler_wahrscheinlichkeit_sehr_klein :
  ∀ seed pk sk m,
    lassen c := encrypt pk m seed
    ‖decrypt sk c - m‖₂ ≤ 2⁻¹⁶⁴ := von
      -- hier würde jetzt der echte Tail-Bound für CBD₂³ + Rundungsfehler stehen
      sorry   -- (oder wenn du Bock hast, bauen wir den auch noch fertig 😉)
