import OMAReductions.R_FeitThompsonPrimeConjecture_feit_thompson_primes_R1

-- Step FeitThompsonPrimeConjecture.feit_thompson_primes.R1.H1
-- Credit: @GiridhariPradeep

theorem OMA.solution : OMA.R_FeitThompsonPrimeConjecture_feit_thompson_primes_R1.H1 := by
  intro p q hp hq hpq hqp hdvd
  haveI := Fact.mk hp
  rw [← Nat.geomSum_eq hq.two_le, ← Nat.geomSum_eq hp.two_le] at hdvd
  have hA : p ∣ ∑ i ∈ Finset.range p, q ^ i := by
    rw [← ZMod.natCast_eq_zero_iff]
    have hq1 : (q : ZMod p) = 1 := by
      rw [← ZMod.natCast_mod, hqp, Nat.cast_one]
    push_cast
    simp [hq1]
  have hB : ¬ p ∣ ∑ i ∈ Finset.range q, p ^ i := by
    rw [← ZMod.natCast_eq_zero_iff]
    obtain ⟨r, hr⟩ : ∃ r, q = r + 1 := ⟨q - 1, by have := hq.one_lt; omega⟩
    rw [hr, Finset.sum_range_succ']
    push_cast
    simp
  exact hB (hA.trans hdvd)
