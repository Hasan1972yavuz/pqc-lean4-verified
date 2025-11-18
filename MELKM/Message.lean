import MLKEM.Rounding

namespace MLKEM1024

/-- ByteEncode₁ / ByteDecode₁ nach FIPS 203 Table 3 -/
def ByteEncode1 (b : Fin 2) : Fin 256 → ℤ
  | i => if i % 2 = 0 then b.val else if i % 2 = 1 then b.val <<< 4 else 0

def ByteDecode1 (f : Fin 256 → ℤ) : Fin 2 :=
  ⟨ (f 0 + (f 1 <<< 4)) % 2, by decide ⟩

theorem decode_encode1 (b : Fin 2) :
    ByteDecode1 (ByteEncode1 b) = b := by
  simp [ByteEncode1, ByteDecode1]
  cases b using Fin.cases <;> rfl

/-- Message Encode/Decode (32 Byte ↔ Polynomial mit Koeff 0/1) -/
def MessageEncode (m : Fin 256 → Bool) : R :=
  ∑ i, if m i then X^i else 0

def MessageDecode (p : R) : Fin 256 → Bool :=
  fun i => p.coeff i = 1

theorem decode_encode_message (m : Fin 256 → Bool) :
    MessageDecode (MessageEncode m) = m := by
  ext i
  simp [MessageDecode, MessageEncode, Polynomial.coeff_sum]
  split <;> simp [*]

end MLKEM1024
