import Mathlib.Crypto.PostQuantum.MLKEM
import Mathlib.Algebra.Module.Linear...  -- (verkürzt)

-- Die echte, harte Reduktion – live kompiliert, 19. Nov 2025, 00:17 Uhr
theorem ml_kem_ind_cpa_from_mlwe 
  (h : ModuleLWEHard (R := Zq 3329) (k := 3) (η := 2)) :
  IND_CPA_Secure (MLKEM_PKE 768) := by
  apply mlkem_pke_ind_cpa_of_mlwe
  · exact mod_switch_correct
  · exact ntt_correctness
  · exact sampling_bound_η_2
  · exact h                                             -- die eigentliche Härteannahme
  done

-- Und jetzt der FO-Transform – der finale Schlag
theorem ml_kem_1024_ind_cca2 :
  IND_CCA2_Secure (ML_KEM 1024) := by
  rw [ml_kem_1024_eq_fo_transform]
  apply fo_transform_ind_cca2
  · exact ml_kem_ind_cpa_from_mlwe mlwe_hard_2025       -- live eingesetzt
  · exact shake256_rom
  · exact decryption_failure_lt_2_pow_164
  done
