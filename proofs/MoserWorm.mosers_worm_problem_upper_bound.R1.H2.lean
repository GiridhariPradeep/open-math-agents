import OMAReductions.R_MoserWorm_mosers_worm_problem_upper_bound_R1

-- Step H2 of reduction MoserWorm.mosers_worm_problem_upper_bound.R1: the triangle
-- {0 ≤ y, |x|/A + y/B ≤ 1} with A = 129/500, B = 501/500 has area A B = 64629/250000.
-- Each vertical slice is an interval [0, B - B|x|/A]; integrate its length over [-A, A].
-- Credit: @GiridhariPradeep (agent: Claude Code)

open MeasureTheory Set intervalIntegral

theorem OMA.integral_tent (A B : ℝ) (hA : 0 < A) :
    ∫ x in (-A)..A, (B - B * |x| / A) = A * B := by
  have h1 : ∫ x in (-A)..0, (B - B * |x| / A) = ∫ x in (-A)..0, (B + B / A * x) := by
    refine integral_congr fun x hx => ?_
    rw [uIcc_of_le (by linarith)] at hx
    rw [abs_of_nonpos hx.2]
    ring
  have h2 : ∫ x in (0:ℝ)..A, (B - B * |x| / A) = ∫ x in (0:ℝ)..A, (B - B / A * x) := by
    refine integral_congr fun x hx => ?_
    rw [uIcc_of_le hA.le] at hx
    rw [abs_of_nonneg hx.1]
    ring
  have hi : IntervalIntegrable (fun x : ℝ => B - B * |x| / A) volume (-A) A :=
    (by fun_prop : Continuous fun x : ℝ => B - B * |x| / A).intervalIntegrable _ _
  rw [← integral_add_adjacent_intervals (b := 0)
    ((by fun_prop : Continuous fun x : ℝ => B - B * |x| / A).intervalIntegrable _ _)
    ((by fun_prop : Continuous fun x : ℝ => B - B * |x| / A).intervalIntegrable _ _), h1, h2]
  rw [integral_add (by simp) ((intervalIntegrable_id).const_mul _),
    integral_sub (by simp) ((intervalIntegrable_id).const_mul _)]
  simp only [integral_const, integral_const_mul, integral_id, smul_eq_mul]
  field_simp
  ring

theorem OMA.solution : OMA.R_MoserWorm_mosers_worm_problem_upper_bound_R1.H2 := by
  show volume {x : ℝ² | 0 ≤ x 1 ∧ |x 0| / (129 / 500 : ℝ) + x 1 / (501 / 500 : ℝ) ≤ 1} =
    ENNReal.ofReal (64629 / 250000 : ℝ)
  set A : ℝ := 129 / 500 with hAdef
  set B : ℝ := 501 / 500 with hBdef
  have hA : 0 < A := by norm_num [hAdef]
  have hB : 0 < B := by norm_num [hBdef]
  let T : Set (ℝ × ℝ) := {p | 0 ≤ p.2 ∧ |p.1| / A + p.2 / B ≤ 1}
  have hTm : MeasurableSet T := by
    refine (measurableSet_le measurable_const measurable_snd).inter
      (measurableSet_le (by fun_prop) measurable_const)
  have hmp := (PiLp.volume_preserving_ofLp (Fin 2)).trans (volume_preserving_finTwoArrow ℝ)
  have hpre : {x : ℝ² | 0 ≤ x 1 ∧ |x 0| / A + x 1 / B ≤ 1} =
      (⇑MeasurableEquiv.finTwoArrow ∘ WithLp.ofLp) ⁻¹' T := by
    ext x
    simp [T, MeasurableEquiv.finTwoArrow, Equiv.finTwoArrow]
  rw [hpre, hmp.measure_preimage hTm.nullMeasurableSet, Measure.volume_eq_prod,
    Measure.prod_apply hTm]
  have hslice : ∀ u : ℝ, Prod.mk u ⁻¹' T = Icc 0 (B - B * |u| / A) := by
    intro u
    ext y
    simp only [T, mem_preimage, mem_setOf_eq, mem_Icc]
    constructor
    · rintro ⟨h1, h2⟩
      refine ⟨h1, ?_⟩
      have : y / B ≤ 1 - |u| / A := by linarith
      rw [div_le_iff₀ hB] at this
      have e : (1 - |u| / A) * B = B - B * |u| / A := by ring
      linarith
    · rintro ⟨h1, h2⟩
      refine ⟨h1, ?_⟩
      have : y / B ≤ 1 - |u| / A := by
        rw [div_le_iff₀ hB]
        have e : (1 - |u| / A) * B = B - B * |u| / A := by ring
        linarith
      linarith
  simp_rw [hslice, Real.volume_Icc, sub_zero]
  -- restrict to [-A, A], where the integrand is nonnegative
  have hsupp : ∀ u : ℝ, u ∉ Icc (-A) A → ENNReal.ofReal (B - B * |u| / A) = 0 := by
    intro u hu
    apply ENNReal.ofReal_of_nonpos
    have hu' : A < |u| := by
      rw [mem_Icc, not_and_or, not_le, not_le] at hu
      rcases hu with h | h
      · rw [abs_of_neg (by linarith)]; linarith
      · rw [abs_of_pos (by linarith)]; exact h
    have : B * A ≤ B * |u| := by nlinarith
    rw [sub_nonpos, le_div_iff₀ hA]
    linarith
  have hfun : (fun u : ℝ => ENNReal.ofReal (B - B * |u| / A)) =
      (Icc (-A) A).indicator (fun u : ℝ => ENNReal.ofReal (B - B * |u| / A)) := by
    funext u
    by_cases hu : u ∈ Icc (-A) A
    · rw [indicator_of_mem hu]
    · rw [indicator_of_notMem hu, hsupp u hu]
  rw [hfun, lintegral_indicator measurableSet_Icc]
  have hcont : Continuous fun u : ℝ => B - B * |u| / A := by fun_prop
  have hnn : 0 ≤ᵐ[volume.restrict (Icc (-A) A)] fun u : ℝ => B - B * |u| / A := by
    refine ae_restrict_of_forall_mem measurableSet_Icc fun u hu => ?_
    have hu' : |u| ≤ A := abs_le.mpr ⟨hu.1, hu.2⟩
    have : B * |u| ≤ B * A := by nlinarith
    show 0 ≤ B - B * |u| / A
    rw [sub_nonneg, div_le_iff₀ hA]
    linarith
  rw [← ofReal_integral_eq_lintegral_ofReal (hcont.integrableOn_Icc) hnn,
    integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le (by linarith),
    OMA.integral_tent A B hA]
  norm_num [hAdef, hBdef]
