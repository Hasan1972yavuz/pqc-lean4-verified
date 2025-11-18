namespace MLKEM1024

def Compress (d : ℕ) (x : ℤ) : ℤ :=
  ((x * (2^d : ℤ) + q) / (2 * q)) % (2^d)

def Decompress (d : ℕ) (y : ℤ) : ℤ :=
  (y * q * 2 + (1^d)) / (2^d)

-- Beispiele laufen sofort
#eval Compress 10 1234  -- sollte sinnvolle Werte geben
#eval Decompress 10 (Compress 10 1234)
