import OMAReductions.R_Erdos137_erdos_137_variants_perfect_power_R1

-- Step Erdos137.erdos_137.variants.perfect_power.R1.H1: hypothesis H1 of reduction Erdos137.erdos_137.variants.perfect_power.R1
-- Credit: @GiridhariPradeep
-- H1 := ∀ (n x l : ℕ), 2 ≤ l → (∏ m ∈ Ioc n (n + 2), m) ≠ x ^ l

/-!
The product is `(n + 1) * (n + 2)`. The two factors are coprime, so if the product were an
`l`-th power each factor would be one: `n + 1 = a ^ l` and `n + 2 = b ^ l`. But two positive
`l`-th powers with `l ≥ 2` never differ by `1`.
-/

namespace OMA.Erdos137H1

/-- Two `l`-th powers (`l ≥ 2`, base `a ≥ 1`) never differ by one. -/
lemma pow_add_one_ne (a b k : ℕ) (ha : 1 ≤ a) : a ^ (k + 2) + 1 ≠ b ^ (k + 2) := by
  intro h
  have hlt : a ^ (k + 2) < b ^ (k + 2) := by omega
  have hab : a < b := lt_of_pow_lt_pow_left₀ (k + 2) (Nat.zero_le _) hlt
  have hle : (a + 1) ^ (k + 2) ≤ b ^ (k + 2) := Nat.pow_le_pow_left hab (k + 2)
  have h1 : a ^ k ≤ (a + 1) ^ k := Nat.pow_le_pow_left (by omega) k
  have h2 : 1 ≤ a ^ k := Nat.one_le_pow _ _ (by omega)
  have e1 : (a + 1) ^ (k + 2) = (a + 1) ^ k * (a + 1) ^ 2 := pow_add _ _ _
  have e2 : a ^ (k + 2) = a ^ k * a ^ 2 := pow_add _ _ _
  have h3 : a ^ k * (a + 1) ^ 2 ≤ (a + 1) ^ k * (a + 1) ^ 2 := Nat.mul_le_mul_right _ h1
  nlinarith

end OMA.Erdos137H1

theorem OMA.solution : OMA.R_Erdos137_erdos_137_variants_perfect_power_R1.H1 := by
  intro n x l hl h
  have hprod : (∏ m ∈ Finset.Ioc n (n + 2), m) = (n + 1) * (n + 2) := by
    rw [Finset.prod_Ioc_succ_top (by omega), Finset.prod_Ioc_succ_top (le_refl n),
      Finset.Ioc_self, Finset.prod_empty, one_mul]
  rw [hprod] at h
  have hcop : Nat.gcd (n + 1) (n + 2) = 1 := by
    show Nat.gcd (n + 1) ((n + 1) + 1) = 1
    simp
  have hu : IsUnit (gcd (n + 1) (n + 2)) := by
    rw [show gcd (n + 1) (n + 2) = Nat.gcd (n + 1) (n + 2) from rfl, hcop]
    exact isUnit_one
  have hu' : IsUnit (gcd (n + 2) (n + 1)) := by rwa [gcd_comm]
  obtain ⟨a, ha⟩ := exists_eq_pow_of_mul_eq_pow hu h
  obtain ⟨b, hb⟩ := exists_eq_pow_of_mul_eq_pow hu' ((mul_comm _ _).trans h)
  obtain ⟨k, rfl⟩ : ∃ k, l = k + 2 := ⟨l - 2, by omega⟩
  have ha1 : 1 ≤ a := by
    rcases Nat.eq_zero_or_pos a with h0 | h0
    · subst h0
      simp at ha
    · exact h0
  exact OMA.Erdos137H1.pow_add_one_ne a b k ha1 (by rw [← ha, ← hb])
