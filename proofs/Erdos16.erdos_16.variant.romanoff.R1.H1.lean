import OMAReductions.R_Erdos16_erdos_16_variant_romanoff_R1

-- Step Erdos16.erdos_16.variant.romanoff.R1.H1
-- Credit: @GiridhariPradeep

open Real

namespace OMA.Sol16

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

end OMA.Sol16

open OMA.Sol16 in
theorem OMA.solution : OMA.R_Erdos16_erdos_16_variant_romanoff_R1.H1 := by
  classical
  refine ⟨1 / 30, by norm_num, 520, ?_⟩
  intro x hx
  set a := x / 2 with ha
  have ha256 : 256 ≤ a := by omega
  have ha0 : a ≠ 0 := by omega
  set L := Nat.log 2 a with hL
  set P := (a.primesBelow).erase 2 with hPdef
  set K := Finset.Icc 1 L with hK
  -- rewrite the sum as the size of a sigma set
  set T : ℕ → Finset ℕ := fun n => (Finset.range n).filter (fun k => 1 ≤ k ∧ 2 ^ k < n ∧
      (n - 2 ^ k).Prime ∧ n - 2 ^ k ≠ 2) with hT
  have hsum : (∑ n ∈ Finset.range (x + 1), ((T n).card : ℝ)) =
      (((Finset.range (x + 1)).sigma T).card : ℝ) := by
    rw [Finset.card_sigma]; push_cast; rfl
  show (1 / 30 : ℝ) * x ≤ ∑ n ∈ Finset.range (x + 1), ((T n).card : ℝ)
  rw [hsum]
  have hinj : (P ×ˢ K).card ≤ ((Finset.range (x + 1)).sigma T).card := by
    refine Finset.card_le_card_of_injOn (fun q => (⟨q.1 + 2 ^ q.2, q.2⟩ : Σ _ : ℕ, ℕ)) ?_ ?_
    · intro q hq
      obtain ⟨hq1, hq2⟩ := Finset.mem_product.mp (Finset.mem_coe.mp hq)
      have hp2 : q.1 ≠ 2 := Finset.ne_of_mem_erase hq1
      have hp := Nat.mem_primesBelow.mp (Finset.mem_of_mem_erase hq1)
      obtain ⟨hk1, hkL⟩ := Finset.mem_Icc.mp hq2
      have hCk : 2 ^ q.2 ≤ a :=
        (Nat.pow_le_pow_right (by norm_num) hkL).trans (Nat.pow_log_le_self 2 ha0)
      have hk2 : q.2 < 2 ^ q.2 := Nat.lt_two_pow_self
      have hp0 := hp.2.pos
      have hpa := hp.1
      rw [Finset.mem_coe, Finset.mem_sigma]
      dsimp only
      refine ⟨Finset.mem_range.mpr (by omega), Finset.mem_filter.mpr
        ⟨Finset.mem_range.mpr (by omega), hk1, by omega, ?_, ?_⟩⟩
      · rw [Nat.add_sub_cancel]; exact hp.2
      · rw [Nat.add_sub_cancel]; exact hp2
    · intro q hq r hr hqr
      simp only [Sigma.mk.injEq] at hqr
      obtain ⟨h1, h2⟩ := hqr
      have h2' : q.2 = r.2 := eq_of_heq h2
      rw [h2'] at h1
      exact Prod.ext (by omega) h2'
  refine le_trans ?_ (Nat.cast_le.mpr hinj)
  rw [Finset.card_product, hK, Nat.card_Icc, hPdef]
  have h2mem : 2 ∈ a.primesBelow := Nat.mem_primesBelow.mpr ⟨by omega, Nat.prime_two⟩
  rw [Finset.card_erase_of_mem h2mem, Nat.primesBelow_card_eq_primeCounting',
    ← Nat.primeCounting_sub_one]
  have hπ1 : 1 ≤ Nat.primeCounting (a - 1) := by
    rw [Nat.primeCounting_sub_one, ← Nat.primesBelow_card_eq_primeCounting']
    exact Finset.card_pos.mpr ⟨2, h2mem⟩
  rw [Nat.add_sub_cancel]
  push_cast [hπ1]
  -- real estimates
  set A : ℝ := (a : ℝ) with hA
  have hA256 : (256 : ℝ) ≤ A := by rw [hA]; exact_mod_cast ha256
  have hxA : (x : ℝ) ≤ 3 * A := by
    have : x ≤ 3 * a := by omega
    rw [hA]; exact_mod_cast this
  have hcast : ((a - 1 : ℕ) : ℝ) = A - 1 := by
    rw [hA, Nat.cast_sub (by omega), Nat.cast_one]
  have hpsi := Chebyshev.psi_ge (a - 1)
  have hpsi2 := Chebyshev.psi_le_primeCounting_mul_log (a - 1)
  rw [hcast, sub_add_cancel] at hpsi
  rw [hcast] at hpsi2
  set π' : ℝ := ((Nat.primeCounting (a - 1) : ℕ) : ℝ) with hπ'
  have hπ'1 : 1 ≤ π' := by rw [hπ']; exact_mod_cast hπ1
  have hlogA1A : log (A - 1) ≤ log A := Real.log_le_log (by linarith) (by linarith)
  have hlogA0 : 0 < log A := Real.log_pos (by linarith)
  have h2 := Real.log_two_gt_d9
  have h2' := Real.log_two_lt_d9
  have hlog4 : 2 * log 2 ≤ log A := by
    rw [← Real.log_rpow (by norm_num)]
    exact Real.log_le_log (by norm_num) (by norm_num; linarith)
  have hLC : log A < ((L : ℝ) + 1) * log 2 := by
    have h := Nat.lt_pow_succ_log_self (by norm_num : 1 < 2) a
    have h' : A < (2 : ℝ) ^ (L + 1) := by rw [hA]; exact_mod_cast h
    have := Real.log_lt_log (by linarith) h'
    rw [Real.log_pow] at this
    push_cast at this
    linarith
  have hsmall := log_small hA256
  have hPA : A * log 2 / 2 - log A ≤ (π' - 1) * log A := by
    have : π' * log (A - 1) ≤ π' * log A := mul_le_mul_of_nonneg_left hlogA1A (by linarith)
    nlinarith
  have hL2 : log A / 2 ≤ (L : ℝ) * log 2 := by linarith
  have hprod : (π' - 1) * (log A / 2) ≤ (π' - 1) * ((L : ℝ) * log 2) :=
    mul_le_mul_of_nonneg_left hL2 (by linarith)
  -- (π' - 1) L log 2 ≥ A / 10
  have hfin : A / 10 ≤ (π' - 1) * (L : ℝ) * log 2 := by nlinarith
  have hL0 : (0 : ℝ) ≤ (π' - 1) * (L : ℝ) := by positivity
  nlinarith
