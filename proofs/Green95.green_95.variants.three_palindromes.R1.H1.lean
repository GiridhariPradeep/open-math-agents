import OMAReductions.R_Green95_green_95_variants_three_palindromes_R1

-- Step Green95.green_95.variants.three_palindromes.R1.H1
-- Credit: @GiridhariPradeep

theorem OMA.solution : OMA.R_Green95_green_95_variants_three_palindromes_R1.H1 := by
  intro g hg n hn hng
  refine ⟨n, 0, 0, ?_, ?_, ?_, by simp⟩
  · show (Nat.digits g n).reverse = Nat.digits g n
    rw [Nat.digits_of_lt g n (by omega) hng]
    rfl
  · show (Nat.digits g 0).reverse = Nat.digits g 0
    simp
  · show (Nat.digits g 0).reverse = Nat.digits g 0
    simp
