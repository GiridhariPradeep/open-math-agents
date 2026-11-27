import OMAReductions.R_Green37_green_37_lower_bound_R1

-- Step Green37.green_37_lower_bound.R1.H2
-- Credit: @GiridhariPradeep

namespace OMA.SolGreen37b

lemma cover_exists (N k : ℕ) :
    ∃ A : Finset ℕ, Green37.IsAPCover (A : Set ℕ) N k := by
  refine ⟨Finset.range (k * N + 1), ?_⟩
  intro d hd
  refine ⟨0, ((Finset.range k).image (fun i ↦ i * d) : Set ℕ), ?_, ?_, ?_⟩
  · intro x hx
    obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hx
    simp only [Finset.mem_coe, Finset.mem_range] at hi ⊢
    exact Nat.lt_succ_of_le (Nat.mul_le_mul (Nat.le_of_lt hi) hd.2)
  · rw [ENat.card_coe_set_eq, Set.encard_coe_eq_coe_finsetCard,
      Finset.card_image_of_injective _
        (fun _ _ h ↦ Nat.eq_of_mul_eq_mul_right hd.1 h), Finset.card_range]
  · ext x; simp

lemma m_mem (N k : ℕ) : ∃ A : Finset ℕ, A.card = Green37.m N k ∧
    Green37.IsAPCover (A : Set ℕ) N k := by
  obtain ⟨A, hA⟩ := cover_exists N k
  have hne : { m | ∃ A : Finset ℕ, A.card = m ∧ Green37.IsAPCover (A : Set ℕ) N k }.Nonempty :=
    ⟨A.card, A, rfl, hA⟩
  exact Nat.sInf_mem hne

lemma containsAP_mono {A : Set ℕ} {k₁ k₂ d : ℕ} (hd : 1 ≤ d) (hk : k₁ ≤ k₂)
    (h : Set.ContainsAP A k₂ d) : Set.ContainsAP A k₁ d := by
  obtain ⟨a, s, hsA, hs⟩ := h
  refine ⟨a, ((Finset.range k₁).image (fun i ↦ a + i * d) : Set ℕ), ?_, ?_, ?_⟩
  · intro x hx
    obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hx
    apply hsA
    rw [hs.2]
    refine ⟨i, ?_, by simp⟩
    have : i < k₂ := lt_of_lt_of_le (Finset.mem_range.mp hi) hk
    exact_mod_cast this
  · rw [ENat.card_coe_set_eq, Set.encard_coe_eq_coe_finsetCard,
      Finset.card_image_of_injective _
        (fun _ _ h ↦ Nat.eq_of_mul_eq_mul_right hd (Nat.add_left_cancel h)), Finset.card_range]
  · ext x; simp

end OMA.SolGreen37b

open OMA.SolGreen37b in
theorem OMA.solution : OMA.R_Green37_green_37_lower_bound_R1.H2 := by
  intro N k₁ k₂ hk
  obtain ⟨A, hAc, hA⟩ := m_mem N k₂
  rw [← hAc]
  apply Nat.sInf_le
  exact ⟨A, rfl, fun d hd => containsAP_mono hd.1 hk (hA d hd)⟩
