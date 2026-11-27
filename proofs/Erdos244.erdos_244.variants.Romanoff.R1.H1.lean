import OMAReductions.R_Erdos244_erdos_244_variants_Romanoff_R1

-- Step Erdos244.erdos_244.variants.Romanoff.R1.H1
-- Credit: @GiridhariPradeep

open Real

namespace OMA.Sol244

/-- `log A ≤ A log 2 / 2 - log 2` once `A ≥ 64`. -/
lemma log_small {A : ℝ} (hA : 64 ≤ A) : log A ≤ A * log 2 / 2 - log 2 := by
  have hA0 : 0 ≤ A := by linarith
  set s := √A with hs
  have hs2 : s ^ 2 = A := Real.sq_sqrt hA0
  have hs0 : 0 < s := Real.sqrt_pos.mpr (by linarith)
  have hs8 : 8 ≤ s := by
    rw [hs, show (8 : ℝ) = √64 by rw [show (64 : ℝ) = 8 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]]
    exact Real.sqrt_le_sqrt hA
  have hlog : log A = 2 * log s := by
    rw [hs, Real.log_sqrt hA0]; ring
  have hls : log s ≤ s - 1 := Real.log_le_sub_one_of_pos hs0
  have h2 := Real.log_two_gt_d9
  have h2' := Real.log_two_lt_d9
  rw [hlog, ← hs2]
  nlinarith [mul_nonneg (sub_nonneg.mpr hs8) hs0.le]

end OMA.Sol244

open OMA.Sol244 in
theorem OMA.solution : OMA.R_Erdos244_erdos_244_variants_Romanoff_R1.H1 := by
  classical
  intro C hC
  have hlogC : 0 < log (C : ℝ) := Real.log_pos (by exact_mod_cast hC)
  refine ⟨log 2 / (6 * log C), div_pos (Real.log_pos (by norm_num)) (by positivity), 130, ?_⟩
  intro x hx
  set a := x / 2 with ha
  have ha64 : 64 ≤ a := by omega
  have ha0 : a ≠ 0 := by omega
  set L := Nat.log C a with hL
  -- the product set lies inside the filter
  have hsub : a.primesBelow ×ˢ Finset.range (L + 1) ⊆ (Finset.range x ×ˢ Finset.range x).filter
      (fun q : ℕ × ℕ => q.1.Prime ∧ q.1 + C ^ q.2 < x) := by
    intro q hq
    obtain ⟨hq1, hq2⟩ := Finset.mem_product.mp hq
    have hp := Nat.mem_primesBelow.mp hq1
    have hk : q.2 ≤ L := Nat.lt_succ_iff.mp (Finset.mem_range.mp hq2)
    have hCk : C ^ q.2 ≤ a :=
      (Nat.pow_le_pow_right (by omega) hk).trans (Nat.pow_log_le_self C ha0)
    have hk2 : q.2 < C ^ q.2 := Nat.lt_pow_self hC
    refine Finset.mem_filter.mpr ⟨Finset.mem_product.mpr ⟨?_, ?_⟩, hp.2, ?_⟩
    · exact Finset.mem_range.mpr (by omega)
    · exact Finset.mem_range.mpr (by omega)
    · omega
  have hcard := Finset.card_le_card hsub
  rw [Finset.card_product, Nat.primesBelow_card_eq_primeCounting', Finset.card_range,
    ← Nat.primeCounting_sub_one] at hcard
  refine le_trans ?_ (Nat.cast_le.mpr hcard)
  push_cast
  -- real estimates
  set A : ℝ := (a : ℝ) with hA
  have hA64 : (64 : ℝ) ≤ A := by rw [hA]; exact_mod_cast ha64
  have hxA : (x : ℝ) ≤ 3 * A := by
    have : x ≤ 3 * a := by omega
    rw [hA]; exact_mod_cast this
  have hcast : ((a - 1 : ℕ) : ℝ) = A - 1 := by
    rw [hA, Nat.cast_sub (by omega), Nat.cast_one]
  have hpsi := Chebyshev.psi_ge (a - 1)
  have hpsi2 := Chebyshev.psi_le_primeCounting_mul_log (a - 1)
  rw [hcast, sub_add_cancel] at hpsi
  rw [hcast] at hpsi2
  set P : ℝ := ((Nat.primeCounting (a - 1) : ℕ) : ℝ) with hP
  have hP0 : 0 ≤ P := Nat.cast_nonneg _
  have hlogA1 : 0 < log (A - 1) := Real.log_pos (by linarith)
  have hlogA1A : log (A - 1) ≤ log A := Real.log_le_log (by linarith) (by linarith)
  -- (L + 1) log C > log A
  have hLC : log A < ((L : ℝ) + 1) * log C := by
    have h := Nat.lt_pow_succ_log_self hC a
    have h' : A < (C : ℝ) ^ (L + 1) := by rw [hA]; exact_mod_cast h
    have := Real.log_lt_log (by linarith) h'
    rw [Real.log_pow] at this
    push_cast at this
    linarith
  have hsmall := log_small hA64
  have h2 := Real.log_two_gt_d9
  -- P * log A ≥ A log 2 / 2
  have hPA : A * log 2 / 2 ≤ P * log A := by
    have : P * log (A - 1) ≤ P * log A := mul_le_mul_of_nonneg_left hlogA1A hP0
    linarith
  have hkey : A * log 2 / 2 ≤ P * (((L : ℝ) + 1) * log C) := by
    have : P * log A ≤ P * (((L : ℝ) + 1) * log C) := mul_le_mul_of_nonneg_left hLC.le hP0
    linarith
  rw [div_mul_eq_mul_div, div_le_iff₀ (by positivity)]
  nlinarith [Real.log_pos (by norm_num : (1 : ℝ) < 2)]
