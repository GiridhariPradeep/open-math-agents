import OMAReductions.R_FeitThompsonPrimeConjecture_feit_thompson_primes_R1

-- Step FeitThompsonPrimeConjecture.feit_thompson_primes.R1.H2
-- Credit: @GiridhariPradeep

theorem OMA.solution : OMA.R_FeitThompsonPrimeConjecture_feit_thompson_primes_R1.H2 := by
  intro p q hp hq hpq hqp hp4 hq4 hdvd
  have hfact : Fact p.Prime := ⟨hp⟩
  rw [← Nat.geomSum_eq hq.two_le, ← Nat.geomSum_eq hp.two_le] at hdvd
  set N := ∑ i ∈ Finset.range p, q ^ i with hN
  set M := ∑ i ∈ Finset.range q, p ^ i with hM
  -- N ≡ 1 (mod p)
  have hNp : N % p = 1 := by
    have hq1 : (q : ZMod p) - 1 ≠ 0 := by
      intro h
      apply hqp
      have h' : ((q : ℕ) : ZMod p) = ((1 : ℕ) : ZMod p) := by
        rw [Nat.cast_one]; exact sub_eq_zero.mp h
      rw [ZMod.natCast_eq_natCast_iff'] at h'
      rw [h', Nat.mod_eq_of_lt hp.one_lt]
    have hgeom : (N : ZMod p) * ((q : ZMod p) - 1) = (q : ZMod p) ^ p - 1 := by
      rw [hN]; push_cast; exact geom_sum_mul _ _
    rw [ZMod.pow_card] at hgeom
    have h1 : (N : ZMod p) = ((1 : ℕ) : ZMod p) := by
      rw [Nat.cast_one]
      have := mul_right_cancel₀ hq1 (hgeom.trans (one_mul _).symm)
      exact this
    rw [ZMod.natCast_eq_natCast_iff', Nat.mod_eq_of_lt hp.one_lt] at h1
    exact h1
  -- N ≡ 3 (mod 4)
  have hN4 : N % 4 = 3 := by
    have hq1 : (q : ZMod 4) = 1 := by
      have : ((q : ℕ) : ZMod 4) = ((1 : ℕ) : ZMod 4) := by
        rw [ZMod.natCast_eq_natCast_iff']; omega
      simpa using this
    have h3 : (N : ZMod 4) = ((3 : ℕ) : ZMod 4) := by
      rw [hN]; push_cast; rw [hq1]; simp only [one_pow, Finset.sum_const, Finset.card_range,
        nsmul_eq_mul, mul_one]
      rw [(ZMod.natCast_eq_natCast_iff' p 3 4).mpr (by omega)]
      norm_num
    rw [ZMod.natCast_eq_natCast_iff'] at h3
    omega
  -- p ^ q ≡ 1 (mod N)
  have hpow : ((p : ℤ) ^ q) % (N : ℤ) = 1 % (N : ℤ) := by
    have hM0 : (M : ZMod N) = 0 := (ZMod.natCast_eq_zero_iff M N).mpr hdvd
    have hgeom : (M : ZMod N) * ((p : ZMod N) - 1) = (p : ZMod N) ^ q - 1 := by
      rw [hM]; push_cast; exact geom_sum_mul _ _
    rw [hM0, zero_mul] at hgeom
    have h1 : (((p : ℤ) ^ q : ℤ) : ZMod N) = ((1 : ℤ) : ZMod N) := by
      push_cast; exact (sub_eq_zero.mp hgeom.symm)
    exact (ZMod.intCast_eq_intCast_iff' _ _ _).mp h1
  have hJpow : jacobiSym (p : ℤ) N ^ q = 1 := by
    rw [← jacobiSym.pow_left, jacobiSym.mod_left' hpow, jacobiSym.one_left]
  have hcop : Int.gcd (p : ℤ) (N : ℤ) = 1 := by
    rw [Int.gcd_natCast_natCast]
    apply (Nat.Prime.coprime_iff_not_dvd hp).mpr
    intro h
    have h0 := Nat.mod_eq_zero_of_dvd h
    omega
  have hqodd : Odd q := Nat.odd_iff.mpr (by omega)
  have hJ1 : jacobiSym (p : ℤ) N = 1 := by
    rcases jacobiSym.eq_one_or_neg_one hcop with h | h
    · exact h
    · rw [h, hqodd.neg_one_pow] at hJpow
      norm_num at hJpow
  have hrec := jacobiSym.quadratic_reciprocity_three_mod_four hp4 hN4
  have hJN : jacobiSym (N : ℤ) p = 1 := by
    rw [jacobiSym.mod_left]
    have : (N : ℤ) % (p : ℤ) = 1 := by
      have := congrArg (fun n : ℕ => (n : ℤ)) hNp
      push_cast at this
      exact this
    rw [this, jacobiSym.one_left]
  rw [hJ1, hJN] at hrec
  norm_num at hrec
