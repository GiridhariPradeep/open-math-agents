import OMAReductions.R_SternPrime_isSternPrime_iff_R1

-- Step SternPrime.isSternPrime_iff.R1.H2: hypothesis H2 of reduction SternPrime.isSternPrime_iff.R1
-- Credit: @GiridhariPradeep
-- H2 := ∀ q : ℕ, q ∈ ({2, 3, 17, 137, 227, 977, 1187, 1493} : Set ℕ) →     SternPrime.IsSternPrime q

/-!
The finite half is the upstream verified lemma `SternPrime.isSternPrime_known_examples`
(a kernel computation over the list of the eight known Stern primes); it only remains to pass
from membership in the `Set` to membership in the `List`.
-/

theorem OMA.solution : OMA.R_SternPrime_isSternPrime_iff_R1.H2 := by
  intro q hq
  apply SternPrime.isSternPrime_known_examples
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hq
  rcases hq with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp
