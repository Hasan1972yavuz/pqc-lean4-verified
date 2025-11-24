namespace Falcon

structure Signature where
  msg : Nat
  sig : Nat
deriving Repr

def sign (msg key : Nat) : Signature :=
  { msg := msg, sig := msg + key }

def verify (key : Nat) (s : Signature) : Bool :=
  s.sig = s.msg + key

theorem verify_correct (msg key : Nat) :
  verify key (sign msg key) = true := by
  simp [verify, sign]

end Falcon
