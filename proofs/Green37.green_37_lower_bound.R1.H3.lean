import OMAReductions.R_Green37_green_37_lower_bound_R1

-- Step Green37.green_37_lower_bound.R1.H3
-- Credit: @GiridhariPradeep

namespace OMA.SolGreen37

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

lemma first_mem {A : Finset ℕ} {k d : ℕ} (hk : 1 ≤ k)
    (h : Set.ContainsAP (A : Set ℕ) k d) : ∃ a, a ∈ A ∧ (2 ≤ k → a + d ∈ A) := by
  obtain ⟨a, s, hsA, hs⟩ := h
  refine ⟨a, ?_, ?_⟩
  · have : a ∈ s := by
      rw [hs.2]
      refine ⟨0, ?_, by simp⟩
      exact_mod_cast hk
    exact Finset.mem_coe.mp (hsA this)
  · intro hk2
    have : a + d ∈ s := by
      rw [hs.2]
      refine ⟨1, ?_, by simp⟩
      exact_mod_cast hk2
    exact Finset.mem_coe.mp (hsA this)

end OMA.SolGreen37

open OMA.SolGreen37 in
theorem OMA.solution : OMA.R_Green37_green_37_lower_bound_R1.H3 := by
  classical
  refine ⟨?_, ?_⟩
  · intro N hN
    obtain ⟨A, hAc, hA⟩ := m_mem N 1
    obtain ⟨a, ha, -⟩ := first_mem le_rfl (hA 1 ⟨le_rfl, hN⟩)
    rw [← hAc]
    exact Finset.card_pos.mpr ⟨a, ha⟩
  · intro N
    obtain ⟨A, hAc, hA⟩ := m_mem N 2
    have ex : ∀ d, 1 ≤ d ∧ d ≤ N → ∃ a, a ∈ A ∧ a + d ∈ A := by
      intro d hd
      obtain ⟨a, ha, ha2⟩ := first_mem (by norm_num) (hA d hd)
      exact ⟨a, ha, ha2 le_rfl⟩
    let f : ℕ → ℕ := fun d => if h : 1 ≤ d ∧ d ≤ N then Classical.choose (ex d h) else 0
    have hf : ∀ d ∈ Finset.Icc 1 N, f d ∈ A ∧ f d + d ∈ A := by
      intro d hd
      have h : 1 ≤ d ∧ d ≤ N := Finset.mem_Icc.mp hd
      simp only [f, dif_pos h]
      exact Classical.choose_spec (ex d h)
    set T1 := (Finset.Icc 1 N).image (fun d => (f d, f d + d)) with hT1
    set T2 := (Finset.Icc 1 N).image (fun d => (f d + d, f d)) with hT2
    have hc1 : T1.card = N := by
      rw [hT1, Finset.card_image_of_injOn, Nat.card_Icc]
      · omega
      intro x _ y _ hxy
      simp only [Prod.mk.injEq] at hxy
      omega
    have hc2 : T2.card = N := by
      rw [hT2, Finset.card_image_of_injOn, Nat.card_Icc]
      · omega
      intro x _ y _ hxy
      simp only [Prod.mk.injEq] at hxy
      omega
    have hdisj : Disjoint T1 T2 := by
      rw [Finset.disjoint_left]
      intro p hp1 hp2
      obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp hp1
      obtain ⟨y, hy, hxy⟩ := Finset.mem_image.mp hp2
      have := (Finset.mem_Icc.mp hx).1
      have := (Finset.mem_Icc.mp hy).1
      simp only [Prod.mk.injEq] at hxy
      omega
    have hsub : T1 ∪ T2 ⊆ A.offDiag := by
      intro p hp
      rcases Finset.mem_union.mp hp with hp | hp
      · obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp hp
        have h1 := (Finset.mem_Icc.mp hx).1
        rw [Finset.mem_offDiag]
        exact ⟨(hf x hx).1, (hf x hx).2, by omega⟩
      · obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp hp
        have h1 := (Finset.mem_Icc.mp hx).1
        rw [Finset.mem_offDiag]
        exact ⟨(hf x hx).2, (hf x hx).1, by omega⟩
    have hle := Finset.card_le_card hsub
    rw [Finset.card_union_of_disjoint hdisj, hc1, hc2, Finset.offDiag_card, hAc] at hle
    rw [Nat.mul_sub_one]
    omega
