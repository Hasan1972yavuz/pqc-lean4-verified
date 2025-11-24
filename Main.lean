import MLKEM
import Falcon

def main : IO Unit := do
  let kp := MLKEM.keygen 42
  IO.println s!"ML-KEM public key:  {kp.public}"
  IO.println s!"ML-KEM private key: {kp.private}"
  let sig := Falcon.sign 2025 kp.public
  IO.println s!"Falcon verify: {Falcon.verify kp.public sig}"
