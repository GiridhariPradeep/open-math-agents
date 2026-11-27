import OMAReductions.R_Erdos5_erdos_5_variants_merikoski_bounded_gaps_R1

-- Step Erdos5.erdos_5.variants.merikoski_bounded_gaps.R1.H2: hypothesis H2 of reduction Erdos5.erdos_5.variants.merikoski_bounded_gaps.R1
-- Credit: @GiridhariPradeep

open Real Filter

namespace OMA.Sol5H2

lemma log_small {A : ℝ} (hA : 256 ≤ A) : log A ≤ A / 8 := by
  have hA0 : 0 ≤ A := by linarith
  set s := √A with hs
  have hs2 : s ^ 2 = A := Real.sq_sqrt hA0
  have hs0 : 0 < s := Real.sqrt_pos.mpr (by linarith)
  have hs16 : 16 ≤ s := by
    rw [hs, show (16 : ℝ) = √256 by
      rw [show (256 : ℝ) = 16 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]]
    exact Real.sqrt_le_sqrt hA
  have hlog : log A = 2 * log s := by
    rw [hs, Real.log_sqrt hA0]; ring
  have hls : log s ≤ s - 1 := Real.log_le_sub_one_of_pos hs0
  rw [hlog, ← hs2]
  nlinarith [mul_nonneg (sub_nonneg.mpr hs16) hs0.le]

/-- Chebyshev's lower bound in the form `x ≤ 2 π(x) log x`. -/
lemma cheb (x : ℕ) (hx : 256 ≤ x) : (x : ℝ) ≤ 2 * (Nat.primeCounting x : ℝ) * log x := by
  have h1 := Chebyshev.psi_ge x
  have h2 := Chebyshev.psi_le_primeCounting_mul_log x
  have hl2 := Real.log_two_gt_d9
  have hx' : (256 : ℝ) ≤ x := by exact_mod_cast hx
  have h3 := log_small (A := (x : ℝ) + 1) (by linarith)
  nlinarith

/-- Chebyshev's upper bound for the `N`-th prime. -/
lemma nth_le (N : ℕ) (hN : 256 ≤ N) : (Nat.nth Nat.Prime N : ℝ) ≤ 6 * N * log N := by
  have hN' : (256 : ℝ) ≤ N := by exact_mod_cast hN
  have hlogN : log 256 ≤ log N := Real.log_le_log (by norm_num) hN'
  have hl256 : (1 : ℝ) ≤ log 256 := by
    rw [show (256 : ℝ) = 2 ^ 8 by norm_num, Real.log_pow]
    have := Real.log_two_gt_d9
    push_cast; nlinarith
  have hLs := log_small hN'
  set x : ℕ := ⌈5 * (N : ℝ) * log N⌉₊ with hxdef
  have hx1 : 5 * (N : ℝ) * log N ≤ x := Nat.le_ceil _
  have hx2 : (x : ℝ) < 5 * (N : ℝ) * log N + 1 := Nat.ceil_lt_add_one (by positivity)
  have hx256 : 256 ≤ x := by
    have : (256 : ℝ) ≤ x := by nlinarith
    exact_mod_cast this
  have hxpos : (0 : ℝ) < x := by positivity
  -- log x ≤ 2 log N since x ≤ N²
  have hxN : (x : ℝ) ≤ (N : ℝ) ^ 2 := by nlinarith
  have hlogx : log x ≤ 2 * log N := by
    calc log (x : ℝ) ≤ log ((N : ℝ) ^ 2) := Real.log_le_log hxpos hxN
      _ = 2 * log N := by rw [Real.log_pow]; push_cast; ring
  have hc := cheb x hx256
  have hπ : (N : ℝ) < Nat.primeCounting x := by
    by_contra h
    rw [not_lt] at h
    have hx1' : (1 : ℝ) ≤ x := by exact_mod_cast (show 1 ≤ x by omega)
    have hlx0 : 0 ≤ log (x : ℝ) := Real.log_nonneg hx1'
    have : (x : ℝ) ≤ 2 * N * (2 * log N) := by
      calc (x : ℝ) ≤ 2 * (Nat.primeCounting x : ℝ) * log x := hc
        _ ≤ 2 * N * log x := mul_le_mul_of_nonneg_right (by linarith) hlx0
        _ ≤ 2 * N * (2 * log N) := mul_le_mul_of_nonneg_left hlogx (by positivity)
    nlinarith
  have hcount : N < Nat.count Nat.Prime (x + 1) := by
    have : N < Nat.primeCounting x := by exact_mod_cast hπ
    exact this
  have hlt := Nat.nth_lt_of_lt_count hcount
  have hle : (Nat.nth Nat.Prime N : ℝ) ≤ x := by exact_mod_cast Nat.lt_succ_iff.mp hlt
  nlinarith

lemma log_ratio : Tendsto (fun n : ℕ => (log 6 + log (log n)) / log n) atTop (nhds 0) := by
  have hlog : Tendsto (fun n : ℕ => log (n : ℝ)) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have h1 : Tendsto (fun y : ℝ => log y / y) atTop (nhds 0) := by
    simpa using Real.tendsto_pow_log_div_mul_add_atTop 1 0 1 one_ne_zero
  have h2 : Tendsto (fun y : ℝ => log 6 / y) atTop (nhds 0) :=
    tendsto_const_nhds.div_atTop tendsto_id
  have := (h2.add h1).comp hlog
  simp only [add_zero] at this
  refine this.congr' ?_
  filter_upwards with n
  simp [add_div]

end OMA.Sol5H2

open OMA.Sol5H2 in
theorem OMA.solution : OMA.R_Erdos5_erdos_5_variants_merikoski_bounded_gaps_R1.H2 := by
  have hup : Tendsto (fun n : ℕ => 1 + (log 6 + log (log n)) / log n) atTop (nhds 1) := by
    simpa using tendsto_const_nhds.add log_ratio
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hup ?_ ?_
  · filter_upwards [eventually_ge_atTop 2] with n hn
    have hn' : (2 : ℝ) ≤ n := by exact_mod_cast hn
    have hl : 0 < log (n : ℝ) := Real.log_pos (by linarith)
    have hp : (n : ℝ) ≤ Nat.nth Nat.Prime n := by
      exact_mod_cast (show n ≤ Nat.nth Nat.Prime n by have := Nat.add_two_le_nth_prime n; omega)
    rw [le_div_iff₀ hl, one_mul]
    exact Real.log_le_log (by linarith) hp
  · filter_upwards [eventually_ge_atTop 256] with n hn
    have hn' : (256 : ℝ) ≤ n := by exact_mod_cast hn
    have hl : 0 < log (n : ℝ) := Real.log_pos (by linarith)
    have hll : 0 < log (log (n : ℝ)) := by
      apply Real.log_pos
      have : log (256 : ℝ) ≤ log n := Real.log_le_log (by norm_num) hn'
      have h8 : log (256 : ℝ) = 8 * log 2 := by
        rw [show (256 : ℝ) = 2 ^ 8 by norm_num, Real.log_pow]; norm_num
      have := Real.log_two_gt_d9
      linarith
    have hpos : (0 : ℝ) < Nat.nth Nat.Prime n := by
      exact_mod_cast (show 0 < Nat.nth Nat.Prime n by have := Nat.add_two_le_nth_prime n; omega)
    have hb := nth_le n hn
    have hlp : log (Nat.nth Nat.Prime n : ℝ) ≤ log 6 + log n + log (log n) := by
      calc log (Nat.nth Nat.Prime n : ℝ) ≤ log (6 * n * log n) := Real.log_le_log hpos hb
        _ = log 6 + log n + log (log n) := by
          rw [Real.log_mul (by positivity) hl.ne', Real.log_mul (by norm_num) (by positivity)]
    rw [div_le_iff₀ hl, add_mul, one_mul, div_mul_cancel₀ _ hl.ne']
    linarith
