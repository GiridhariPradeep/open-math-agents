import OMAReductions.R_BusyBeaver_BB_4_R1_H2_R1_H1_R1

-- Step BusyBeaver.BB_4.R1.H2.R1.H1.R1.H1: hypothesis H1 of reduction BusyBeaver.BB_4.R1.H2.R1.H1.R1
-- Credit: @GiridhariPradeep

open Turing Turing.BusyBeaver

namespace OMA.SolBB4

/-- Running `a + b` steps is running `a` steps and then `b` more. -/
theorem multiStep_add {Γ Λ : Type*} [Inhabited Λ] [Inhabited Γ] (M : Machine Γ Λ)
    (s : Cfg Γ Λ) (a b : ℕ) :
    M.multiStep s (a + b) = (M.multiStep s a).bind (fun c => M.multiStep c b) := by
  induction b with
  | zero => cases h : M.multiStep s a <;> simp [h]
  | succ b ih =>
    rw [← Nat.add_assoc, Machine.multiStep_succ, ih]
    cases h : M.multiStep s a <;> simp [h, Machine.multiStep_succ]

/-- A configuration seen at steps `i < j` makes the run periodic, so it never stops. -/
theorem never_none {Γ Λ : Type*} [Inhabited Λ] [Inhabited Γ] (M : Machine Γ Λ)
    (s c : Cfg Γ Λ) (i j : ℕ) (hij : i < j)
    (hi : M.multiStep s i = some c) (hj : M.multiStep s j = some c) :
    ∀ n, M.multiStep s n ≠ none := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    by_cases hn : n < j
    · intro h
      have := Machine.multiStep_eq_none_mono h hn.le
      rw [hj] at this
      exact Option.some_ne_none _ this
    · obtain ⟨d, rfl⟩ : ∃ d, n = j + d := ⟨n - j, by omega⟩
      have e1 : M.multiStep s (j + d) = M.multiStep s (i + d) := by
        rw [multiStep_add, hj, multiStep_add, hi]
      rw [e1]
      exact ih _ (by omega)

end OMA.SolBB4

theorem OMA.solution : OMA.R_BusyBeaver_BB_4_R1_H2_R1_H1_R1.H1 := by
  rintro M - ⟨i, j, hij, -, c, hi, -, hj, -⟩
  rw [Machine.not_isHalting_iff_forall_isSome_multiStep]
  intro n
  rw [Option.isSome_iff_ne_none]
  exact OMA.SolBB4.never_none M _ c i j hij hi hj (n + 1)
