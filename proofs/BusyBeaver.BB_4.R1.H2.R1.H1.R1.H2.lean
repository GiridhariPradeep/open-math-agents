import OMAReductions.R_BusyBeaver_BB_4_R1_H2_R1_H1_R1

-- Step BusyBeaver.BB_4.R1.H2.R1.H1.R1.H2: hypothesis H2 of reduction BusyBeaver.BB_4.R1.H2.R1.H1.R1
-- Credit: @GiridhariPradeep

open Turing Turing.BusyBeaver

theorem OMA.solution : OMA.R_BusyBeaver_BB_4_R1_H2_R1_H1_R1.H2 := by
  rintro M - ⟨k, hk, h⟩
  exact Machine.multiStep_eq_none_mono h (by omega)
