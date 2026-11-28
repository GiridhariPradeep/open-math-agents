import OMAReductions.R_Erdos360_erdos_360_R1_H4_R1_H3_R1

-- Step H2 of reduction Erdos360.erdos_360.R1.H4.R1.H3.R1: gluing. If the sums over I cover an
-- interval of length w ≥ D - 1, each new summand j with x + p ≤ y ≤ x + D in S j extends it by p:
-- the two translates by x and by y overlap, since y - x ≤ D ≤ w + 1. Induction on T.
-- Credit: @GiridhariPradeep (agent: Claude Code)

open scoped BigOperators

theorem OMA.glue_aux (n : ℕ) (S : Fin n → Finset ℕ) (I : Finset (Fin n)) (a w D p : ℕ)
    (hD : D ≤ w + 1)
    (hcov : ∀ t ∈ Finset.Icc a (a+w), ∃ f : Fin n → ℕ, (∀ i ∈ I, f i ∈ S i) ∧ ∑ i ∈ I, f i = t) :
    ∀ T : Finset (Fin n), Disjoint I T →
    (∀ i ∈ T, ∃ x ∈ S i, ∃ y ∈ S i, x+p ≤ y ∧ y ≤ x+D) →
    ∃ b : ℕ, ∀ t ∈ Finset.Icc b (b+(w+T.card*p)), ∃ f : Fin n → ℕ,
      (∀ i ∈ I ∪ T, f i ∈ S i) ∧ ∑ i ∈ I ∪ T, f i = t := by
  classical
  intro T
  induction T using Finset.induction_on with
  | empty =>
    intro _ _
    refine ⟨a, fun t ht => ?_⟩
    simp only [Finset.card_empty, zero_mul, add_zero, Finset.union_empty] at ht ⊢
    exact hcov t ht
  | insert j T hjT ih =>
    intro hdisj hT
    have hdisj' : Disjoint I T := Finset.disjoint_of_subset_right (Finset.subset_insert j T) hdisj
    obtain ⟨b, hb⟩ := ih hdisj' (fun i hi => hT i (Finset.mem_insert_of_mem hi))
    obtain ⟨x, hx, y, hy, hxy, hyx⟩ := hT j (Finset.mem_insert_self j T)
    have hjI : j ∉ I := fun h => Finset.disjoint_left.mp hdisj h (Finset.mem_insert_self j T)
    have hjU : j ∉ I ∪ T := by
      rw [Finset.mem_union]
      rintro (h | h)
      · exact hjI h
      · exact hjT h
    have hcard : (insert j T).card = T.card + 1 := Finset.card_insert_of_notMem hjT
    have hmul : (T.card + 1) * p = T.card * p + p := by ring
    refine ⟨b + x, fun t ht => ?_⟩
    rw [hcard, Finset.mem_Icc] at ht
    have key : ∃ v ∈ S j, ∃ s ∈ Finset.Icc b (b + (w + T.card * p)), t = s + v := by
      by_cases hle : t ≤ b + x + (w + T.card * p)
      · exact ⟨x, hx, t - x, Finset.mem_Icc.mpr ⟨by omega, by omega⟩, by omega⟩
      · refine ⟨y, hy, t - y, Finset.mem_Icc.mpr ⟨by omega, by omega⟩, by omega⟩
    obtain ⟨v, hv, s, hs, rfl⟩ := key
    obtain ⟨f, hfS, hfsum⟩ := hb s hs
    refine ⟨Function.update f j v, ?_, ?_⟩
    · intro i hi
      rw [Finset.union_insert, Finset.mem_insert] at hi
      by_cases hij : i = j
      · subst hij
        simp [hv]
      · rw [Function.update_of_ne hij]
        rcases hi with h | h
        · exact absurd h hij
        · exact hfS i h
    · rw [Finset.union_insert, Finset.sum_insert hjU, Function.update_self]
      rw [Finset.sum_congr rfl (fun i hi => Function.update_of_ne
        (fun h => hjU (h ▸ hi)) v f)]
      rw [hfsum]
      ring

theorem OMA.solution : OMA.R_Erdos360_erdos_360_R1_H4_R1_H3_R1.H2 := by
  intro n S I T a w D p hdisj hD hT hcov
  exact OMA.glue_aux n S I a w D p hD hcov T hdisj hT
