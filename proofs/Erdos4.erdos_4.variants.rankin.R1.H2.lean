import OMAReductions.R_Erdos4_erdos_4_variants_rankin_R1

-- Step Erdos4.erdos_4.variants.rankin.R1.H2: hypothesis H2 of reduction Erdos4.erdos_4.variants.rankin.R1
-- Credit: @GiridhariPradeep
-- H2 := ∃ N : ℕ, ∀ x : ℕ, N ≤ x → x ≤ Nat.primeCounting x ^ 2

/-!
From Mathlib's Chebyshev bounds, `x log 2 - log (x + 1) ≤ ψ x ≤ π x · log x`.
Writing `x = s ^ 4` and using `log s ≤ s - 1`, for `x ≥ 4096` (so `s ≥ 8`) the left side exceeds
`s ^ 2 · log x = √x · log x`, hence `π x > √x` and `x ≤ π x ^ 2`.
-/

theorem OMA.solution : OMA.R_Erdos4_erdos_4_variants_rankin_R1.H2 := by
  refine ⟨4096, fun x hx => ?_⟩
  have hxr : (4096 : ℝ) ≤ x := by exact_mod_cast hx
  set s := Real.sqrt (Real.sqrt (x : ℝ)) with hs
  have hs0 : 0 ≤ s := Real.sqrt_nonneg _
  have hsq : s ^ 2 = Real.sqrt x := Real.sq_sqrt (Real.sqrt_nonneg _)
  have hsq2 : (Real.sqrt (x : ℝ)) ^ 2 = x := Real.sq_sqrt (by positivity)
  have hs4 : s ^ 4 = x := by rw [show s ^ 4 = (s ^ 2) ^ 2 by ring, hsq, hsq2]
  have hs8 : 8 ≤ s := by
    by_contra h
    rw [not_le] at h
    have h' := pow_lt_pow_left₀ h hs0 (by norm_num : (4 : ℕ) ≠ 0)
    norm_num at h'
    linarith
  have hspos : 0 < s := by linarith
  have hlogs : Real.log s ≤ s - 1 := Real.log_le_sub_one_of_pos hspos
  have hlogx : Real.log x = 4 * Real.log s := by
    rw [← hs4, Real.log_pow]
    push_cast
    ring
  have hlog1 : Real.log ((x : ℝ) + 1) ≤ Real.log 2 + Real.log x := by
    rw [← Real.log_mul (by norm_num) (by positivity)]
    exact Real.log_le_log (by positivity) (by linarith)
  have hl2 := Real.log_two_gt_d9
  have hl2' := Real.log_two_lt_d9
  have hpsi := Chebyshev.psi_ge x
  have hpc := Chebyshev.psi_le_primeCounting_mul_log x
  have hlogxpos : 0 < Real.log x := Real.log_pos (by linarith)
  have hlogs0 : 0 ≤ Real.log s := Real.log_nonneg (by linarith)
  have key : s ^ 2 * Real.log x < (x : ℝ) * Real.log 2 - Real.log ((x : ℝ) + 1) := by
    have h4 : s ^ 2 * Real.log s ≤ s ^ 2 * (s - 1) :=
      mul_le_mul_of_nonneg_left hlogs (by positivity)
    rw [hlogx] at hlog1 ⊢
    have hA : s ^ 2 * (4 * Real.log s) ≤ 4 * s ^ 3 - 4 * s ^ 2 := by nlinarith
    have hB : Real.log ((x : ℝ) + 1) ≤ 1 + 4 * s := by nlinarith
    have hC : 0.693 * s ^ 4 ≤ (x : ℝ) * Real.log 2 := by
      rw [← hs4]
      have : 0 ≤ s ^ 4 := by positivity
      nlinarith
    have hD : 4 * s ^ 3 - 4 * s ^ 2 + (1 + 4 * s) < 0.693 * s ^ 4 := by
      have h1 : 0 ≤ (s - 8) * s ^ 3 := mul_nonneg (by linarith) (by positivity)
      have h2 : 0 ≤ s ^ 2 := by positivity
      nlinarith
    linarith
  have hpi : s ^ 2 < (Nat.primeCounting x : ℝ) := by
    by_contra h
    rw [not_lt] at h
    have h' : (Nat.primeCounting x : ℝ) * Real.log x ≤ s ^ 2 * Real.log x :=
      mul_le_mul_of_nonneg_right h hlogxpos.le
    linarith
  have hfin : (x : ℝ) < (Nat.primeCounting x : ℝ) ^ 2 := by
    rw [← hs4, show s ^ 4 = (s ^ 2) ^ 2 by ring]
    exact pow_lt_pow_left₀ hpi (by positivity) (by norm_num)
  exact_mod_cast hfin.le
