import OMAReductions.R_Erdos436_erdos_436_variants_seven_two_R1_H3_R1

-- Step Erdos436.erdos_436.variants.seven_two.R1.H3.R1.H2: hypothesis H2 of reduction Erdos436.erdos_436.variants.seven_two.R1.H3.R1
-- Credit: @GiridhariPradeep

/-- In a finite cyclic group of order `n` with `d ∣ n`, the `d`-th powers are exactly the
kernel of `x ↦ x ^ (n / d)`: one contains the other and both have `n / d` elements. -/
theorem OMA.range_pow_eq_ker {G : Type*} [CommGroup G] [IsCyclic G] [Finite G] {d : ℕ}
    (hd : d ∣ Nat.card G) (hd0 : 0 < d) :
    (powMonoidHom d : G →* G).range = (powMonoidHom (Nat.card G / d) : G →* G).ker := by
  have hle : (powMonoidHom d : G →* G).range ≤ (powMonoidHom (Nat.card G / d) : G →* G).ker := by
    rintro _ ⟨y, rfl⟩
    rw [MonoidHom.mem_ker, powMonoidHom_apply, powMonoidHom_apply, ← pow_mul,
      Nat.mul_div_cancel' hd, pow_card_eq_one']
  apply Subgroup.eq_of_le_of_card_ge hle
  rw [IsCyclic.card_powMonoidHom_ker, IsCyclic.card_powMonoidHom_range,
    Nat.gcd_eq_right hd, Nat.gcd_eq_right (Nat.div_dvd_of_dvd hd)]

theorem OMA.solution : OMA.R_Erdos436_erdos_436_variants_seven_two_R1_H3_R1.H2 := by
  intro p hp h7 a ha
  haveI := Fact.mk hp
  constructor
  · rintro ⟨x, rfl⟩
    have hx : x ≠ 0 := by
      rintro rfl
      exact ha (by simp)
    rw [← pow_mul, Nat.mul_div_cancel' h7]
    exact ZMod.pow_card_sub_one_eq_one hx
  · intro h
    let u : (ZMod p)ˣ := Units.mk0 a ha
    have hcard : Nat.card (ZMod p)ˣ = p - 1 := by
      rw [Nat.card_eq_fintype_card, ZMod.card_units_eq_totient, Nat.totient_prime hp]
    have hu : u ∈ (powMonoidHom ((p - 1) / 7) : (ZMod p)ˣ →* (ZMod p)ˣ).ker := by
      rw [MonoidHom.mem_ker, powMonoidHom_apply]
      ext
      simpa [u] using h
    rw [← hcard, ← OMA.range_pow_eq_ker (hcard ▸ h7) (by norm_num)] at hu
    obtain ⟨y, hy⟩ := hu
    refine ⟨(y : ZMod p), ?_⟩
    have := congrArg (fun w : (ZMod p)ˣ => (w : ZMod p)) hy
    simpa [u] using this
