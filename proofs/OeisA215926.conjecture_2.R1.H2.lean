import OMAReductions.R_OeisA215926_conjecture_2_R1

-- Step OeisA215926.conjecture_2.R1.H2
-- Credit: @GiridhariPradeep

theorem OMA.solution : OMA.R_OeisA215926_conjecture_2_R1.H2 := by
  intro j q hq hq2 hqj
  have hn : 0 < 2 ^ j * q := Nat.mul_pos (Nat.two_pow_pos j) hq.pos
  rw [Nat.perfect_iff_sum_divisors_eq_two_mul hn, Nat.abundant_iff_sum_divisors]
  have hcop : Nat.Coprime (2 ^ j) q := by
    apply Nat.Coprime.pow_left
    rw [Nat.coprime_primes Nat.prime_two hq]
    omega
  rw [hcop.sum_divisors_mul, Nat.sum_divisors_prime_pow Nat.prime_two, hq.divisors,
    Finset.sum_pair (Ne.symm hq.ne_one)]
  have hS := Nat.geomSum_eq (le_refl 2) (j + 1)
  set S := ∑ i ∈ Finset.range (j + 1), 2 ^ i with hSdef
  have hT : 1 ≤ 2 ^ j := Nat.one_le_two_pow
  have hS1 : S + 1 = 2 * 2 ^ j := by
    rw [hS, pow_succ]; simp; omega
  have : 2 * (2 ^ j * q) ≤ S * (1 + q) := by nlinarith
  omega
