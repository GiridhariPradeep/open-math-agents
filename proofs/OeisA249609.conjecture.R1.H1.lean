import OMAReductions.R_OeisA249609_conjecture_R1

-- Step OeisA249609.conjecture.R1.H1: hypothesis H1 of reduction OeisA249609.conjecture.R1
-- Credit: @GiridhariPradeep
-- H1 := ∀ n : ℕ, n ∈ ({0, 1, 2, 7, 8} : Finset ℕ) → OeisA249609.a n = 0

/-!
A direct computation: in rows `0, 1, 2, 7, 8` of Pascal's triangle every binomial coefficient
`C(n, m)` with `1 ≤ m ≤ n` has an odd number of ones in binary, so the search in `a` finds nothing.
-/

theorem OMA.solution : OMA.R_OeisA249609_conjecture_R1.H1 := by
  intro n hn
  simp only [Finset.mem_insert, Finset.mem_singleton] at hn
  rcases hn with rfl | rfl | rfl | rfl | rfl <;> decide
