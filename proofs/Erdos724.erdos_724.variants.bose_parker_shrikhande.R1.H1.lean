import OMAReductions.R_Erdos724_erdos_724_variants_bose_parker_shrikhande_R1

-- Step Erdos724.erdos_724.variants.bose_parker_shrikhande.R1.H1
-- Credit: @GiridhariPradeep

open Erdos724 Fin.CommRing

theorem OMA.solution : OMA.R_Erdos724_erdos_724_variants_bose_parker_shrikhande_R1.H1 := by
  intro n hodd h3
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 3 := ⟨n - 3, by omega⟩
  obtain ⟨t, ht⟩ := hodd
  -- 2 is a unit in Fin (m + 3)
  set h : Fin (m + 3) := (Nat.cast (t + 1) : Fin (m + 3)) with hh
  have hu : h * 2 = 1 := by
    rw [hh, show (2 : Fin (m + 3)) = (Nat.cast 2 : Fin (m + 3)) by simp, ← Nat.cast_mul,
      show (t + 1) * 2 = (m + 3) + 1 by omega, Nat.cast_add, Fin.natCast_self, zero_add,
      Nat.cast_one]
  have two_inj : ∀ a b : Fin (m + 3), 2 * a = 2 * b → a = b := by
    intro a b hab
    calc a = (h * 2) * a := by rw [hu, one_mul]
      _ = h * (2 * a) := mul_assoc h 2 a
      _ = h * (2 * b) := by rw [hab]
      _ = (h * 2) * b := (mul_assoc h 2 b).symm
      _ = b := by rw [hu, one_mul]
  let L : LatinSquare (m + 3) :=
    { mat := fun i j => i + j
      row_injective := fun i j j' hj => add_left_cancel hj
      col_injective := fun j i i' hi => add_right_cancel hi }
  let M : LatinSquare (m + 3) :=
    { mat := fun i j => i + 2 * j
      row_injective := fun i j j' hj => two_inj j j' (add_left_cancel hj)
      col_injective := fun j i i' (hi : i + 2 * j = i' + 2 * j) => add_right_cancel hi }
  refine ⟨L, M, ?_, ?_⟩
  · intro hLM
    have := congrArg (fun K : LatinSquare (m + 3) => K.mat 0 1) hLM
    simp only [L, M, zero_add, mul_one] at this
    have h12 := congrArg Fin.val this
    rw [Fin.val_one, Fin.val_two] at h12
    omega
  · intro p q hpq
    simp only [L, M, Prod.mk.injEq] at hpq
    obtain ⟨h1, h2⟩ := hpq
    have hj : p.2 = q.2 := by linear_combination h2 - h1
    have hi : p.1 = q.1 := by rw [hj] at h1; exact add_right_cancel h1
    exact Prod.ext hi hj
