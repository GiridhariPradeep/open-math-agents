import OMAReductions.R_Erdos828_erdos_828_R1

-- Step Erdos828.erdos_828.R1.H1
-- Credit: @GiridhariPradeep

theorem OMA.solution : OMA.R_Erdos828_erdos_828_R1.H1 := by
  intro a ha
  rcases ha with rfl | ⟨m, hm, hdvd, rfl⟩
  · apply Set.infinite_of_forall_exists_gt
    intro N
    refine ⟨2 ^ (N + 1), ?_, ?_⟩
    · show ((Nat.totient (2 ^ (N + 1)) : ℕ) : ℤ) ∣ ((2 ^ (N + 1) : ℕ) : ℤ) + 0
      rw [add_zero, Nat.totient_prime_pow Nat.prime_two (Nat.succ_pos N)]
      apply Int.natCast_dvd_natCast.mpr
      refine ⟨2, ?_⟩
      simp [pow_succ]
    · exact (Nat.lt_two_pow_self).trans (Nat.pow_lt_pow_right (by norm_num) (Nat.lt_succ_self N))
  · apply Set.infinite_of_forall_exists_gt
    intro N
    obtain ⟨p, hpge, hp⟩ := Nat.exists_infinite_primes (N + m + 1)
    refine ⟨m * p, ?_, ?_⟩
    · show ((Nat.totient (m * p) : ℕ) : ℤ) ∣ ((m * p : ℕ) : ℤ) + -(m : ℤ)
      have hndvd : ¬ p ∣ m := fun h => by
        have := Nat.le_of_dvd hm h
        omega
      have hcop : Nat.Coprime m p := (Nat.Coprime.symm ((Nat.Prime.coprime_iff_not_dvd hp).2 hndvd))
      rw [Nat.totient_mul hcop, Nat.totient_prime hp]
      obtain ⟨c, hc⟩ := hdvd
      have hp1 : 1 ≤ p := hp.one_lt.le
      refine ⟨c, ?_⟩
      have : ((m * p : ℕ) : ℤ) + -(m : ℤ) = (m : ℤ) * ((p : ℤ) - 1) := by push_cast; ring
      rw [this]
      have hcz : (m : ℤ) = (Nat.totient m : ℤ) * (c : ℤ) := by exact_mod_cast hc
      push_cast [hp1]
      rw [hcz]
      ring
    · have : 1 ≤ m := hm
      calc N < p := by omega
        _ ≤ m * p := Nat.le_mul_of_pos_left p hm
