import OMAReductions.R_Erdos91_erdos_91_variants_eight_R1_H1_R1

-- Step Erdos91.erdos_91.variants.eight.R1.H1.R1.H2: hypothesis H2 of reduction Erdos91.erdos_91.variants.eight.R1.H1.R1
-- Credit: @GiridhariPradeep
-- H2 := ∀ (p q : ℝ²) (r d : ℝ), p ≠ q → ∀ W : Finset ℝ²,     (∀ w ∈ W, dist p w = r ∧ dist q w = d) → W.card ≤ 2

/-!
Two circles in the plane with distinct centres meet in at most two points: this is
`EuclideanGeometry.eq_of_dist_eq_of_dist_eq_of_finrank_eq_two` applied to any three points of `W`.
-/

theorem OMA.solution : OMA.R_Erdos91_erdos_91_variants_eight_R1_H1_R1.H2 := by
  intro p q r d hpq W hW
  by_contra hcard
  obtain ⟨a, ha, b, hb, c, hc, hab, hac, hbc⟩ := Finset.two_lt_card.1 (not_le.1 hcard)
  have hd : Module.finrank ℝ (EuclideanSpace ℝ (Fin 2)) = 2 := finrank_euclideanSpace_fin
  have key := EuclideanGeometry.eq_of_dist_eq_of_dist_eq_of_finrank_eq_two (c₁ := p) (c₂ := q)
    (p₁ := a) (p₂ := b) (p := c) (r₁ := r) (r₂ := d) hd hpq hab
    ((dist_comm a p).trans (hW a ha).1) ((dist_comm b p).trans (hW b hb).1)
    ((dist_comm c p).trans (hW c hc).1) ((dist_comm a q).trans (hW a ha).2)
    ((dist_comm b q).trans (hW b hb).2) ((dist_comm c q).trans (hW c hc).2)
  rcases key with h | h
  · exact hac h.symm
  · exact hbc h.symm
