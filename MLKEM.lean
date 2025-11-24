namespace MLKEM

structure Keypair where
  public  : Nat
  private : Nat
deriving Repr

def keygen (seed : Nat) : Keypair :=
  { public  := (seed * 17) % 7919
    private := (seed * 19) % 7919 }

theorem keygen_deterministic (s : Nat) :
  keygen s = keygen s := rfl

end MLKEM
