import OMAReductions.R_OeisA24356_conjecture_R1

-- Step OeisA24356.conjecture.R1.H1: hypothesis H1 of reduction OeisA24356.conjecture.R1
-- Credit: @GiridhariPradeep
-- H1 := OeisA24356.a 4 = 0

/-!
The 4 × 4 Hankel matrix of the primes `2, 3, 5, 7, 11, 13, 17` is singular: the vector
`(6, -3, -2, 1)` is in its kernel. This is the upstream verified computation `OeisA24356.a_4`.
-/

theorem OMA.solution : OMA.R_OeisA24356_conjecture_R1.H1 :=
  OeisA24356.a_4
