import OMAReductions.R_Erdos629_erdos_629_variants_n_three_R1

-- Step Erdos629.erdos_629.variants.n_three.R1.H1: hypothesis H1 of reduction Erdos629.erdos_629.variants.n_three.R1
-- Credit: @GiridhariPradeep
-- H1 := Erdos629.n 3 ≤ 14

/-!
The witness is the complete bipartite graph `K_{7,7}` with the lists given by the lines of the
Fano plane: left vertex `i` and right vertex `i` both get the three points of line `i`.
A list colouring would make the colours `A` used on the left side meet every line, and the
colours used on the right side (which avoid `A`) also meet every line. Then colouring the points
by membership in `A` would be a 2-colouring of the Fano plane with no monochromatic line, which
does not exist.
-/

namespace OMA.Erdos629H1

open SimpleGraph

/-- The seven lines of the Fano plane on the points `0, …, 6`. -/
def line (j : ℕ) : Finset ℕ :=
  match j with
  | 0 => {0, 1, 2}
  | 1 => {0, 3, 4}
  | 2 => {0, 5, 6}
  | 3 => {1, 3, 5}
  | 4 => {1, 4, 6}
  | 5 => {2, 3, 6}
  | _ => {2, 4, 5}

/-- The Fano plane has no proper 2-colouring: some line is monochromatic. -/
lemma fano : ∀ x0 x1 x2 x3 x4 x5 x6 : Bool,
    (x0 = x1 ∧ x1 = x2) ∨ (x0 = x3 ∧ x3 = x4) ∨ (x0 = x5 ∧ x5 = x6) ∨
    (x1 = x3 ∧ x3 = x5) ∨ (x1 = x4 ∧ x4 = x6) ∨ (x2 = x3 ∧ x3 = x6) ∨
    (x2 = x4 ∧ x4 = x5) := by
  decide

/-- Left side relation of `K_{7,7}` on `Fin 14`: vertices `< 7` versus vertices `≥ 7`. -/
def rel (a b : Fin 14) : Prop := (a.val < 7 ∧ 7 ≤ b.val) ∨ (7 ≤ a.val ∧ b.val < 7)

/-- The complete bipartite graph `K_{7,7}`. -/
def G : SimpleGraph (Fin 14) := SimpleGraph.fromRel rel

/-- The left copy of a line index. -/
def lv (i : Fin 7) : Fin 14 := ⟨i.val, by have := i.isLt; omega⟩

/-- The right copy of a line index. -/
def rv (i : Fin 7) : Fin 14 := ⟨i.val + 7, by have := i.isLt; omega⟩

lemma adj_lv_rv (i j : Fin 7) : G.Adj (lv i) (rv j) := by
  have hi := i.isLt
  refine (SimpleGraph.fromRel_adj _ _ _).2 ⟨?_, Or.inl (Or.inl ⟨hi, ?_⟩)⟩
  · intro h
    have h' := congrArg Fin.val h
    simp only [lv, rv] at h'
    omega
  · show 7 ≤ j.val + 7
    omega

lemma colorable : G.Colorable 2 := by
  refine ⟨Coloring.mk (fun v => if v.val < 7 then (0 : Fin 2) else 1) ?_⟩
  intro a b hab
  rw [G, SimpleGraph.fromRel_adj] at hab
  obtain ⟨-, h⟩ := hab
  rcases h with (⟨h1, h2⟩ | ⟨h1, h2⟩) | (⟨h1, h2⟩ | ⟨h1, h2⟩)
  · have h3 : ¬ b.val < 7 := by omega
    simp [h1, h3]
  · have h3 : ¬ a.val < 7 := by omega
    simp [h2, h3]
  · have h3 : ¬ a.val < 7 := by omega
    simp [h1, h3]
  · have h3 : ¬ b.val < 7 := by omega
    simp [h2, h3]

/-- Choosability is monotone in the list size. -/
lemma choosable_mono {V : Type*} {H : SimpleGraph V} {k m : ℕ} (h : H.IsKChoosable k)
    (hkm : k ≤ m) : H.IsKChoosable m := by
  intro L hL
  have hsub : ∀ v, ∃ t ⊆ L v, t.card = k := fun v =>
    Finset.exists_subset_card_eq (by rw [hL v]; exact hkm)
  choose L' hL'sub hL'card using hsub
  obtain ⟨C, hC⟩ := h L' hL'card
  exact ⟨C, fun v => hL'sub v (hC v)⟩

/-- Every graph on `Fin 14` is `14`-choosable: Hall gives a choice of pairwise distinct colours. -/
lemma choosable_14 (H : SimpleGraph (Fin 14)) : H.IsKChoosable 14 := by
  intro L hL
  obtain ⟨f, hf, hfL⟩ := (Finset.all_card_le_biUnion_card_iff_exists_injective L).1 (by
    intro s
    rcases s.eq_empty_or_nonempty with rfl | ⟨v, hv⟩
    · simp
    · calc s.card ≤ 14 := by simpa using Finset.card_le_univ s
        _ = (L v).card := (hL v).symm
        _ ≤ (s.biUnion L).card := Finset.card_le_card (Finset.subset_biUnion_of_mem L hv))
  exact ⟨Coloring.mk f (fun hab heq => H.ne_of_adj hab (hf heq)), hfL⟩

/-- The key combinatorial step for one line `{a, b, c}`. -/
lemma line_contra (A : Finset ℕ) (a b c y z : ℕ) (hy : y ∈ ({a, b, c} : Finset ℕ)) (hyA : y ∈ A)
    (hz : z ∈ ({a, b, c} : Finset ℕ)) (hzA : z ∉ A) (h1 : (a ∈ A ↔ b ∈ A))
    (h2 : (b ∈ A ↔ c ∈ A)) : False := by
  simp only [Finset.mem_insert, Finset.mem_singleton] at hy hz
  rcases hy with rfl | rfl | rfl <;> rcases hz with rfl | rfl | rfl <;> tauto

lemma not_choosable_3 : ¬ G.IsKChoosable 3 := by
  intro h
  obtain ⟨C, hC⟩ := h (fun v => line (v.val % 7)) (by intro v; fin_cases v <;> rfl)
  set A : Finset ℕ := Finset.univ.image (fun i : Fin 7 => C (lv i)) with hA
  have hl : ∀ i : Fin 7, C (lv i) ∈ A := fun i => Finset.mem_image_of_mem _ (Finset.mem_univ i)
  have hr : ∀ j : Fin 7, C (rv j) ∉ A := by
    intro j hj
    rw [hA, Finset.mem_image] at hj
    obtain ⟨i, -, hi⟩ := hj
    exact C.valid (adj_lv_rv i j) hi
  rcases fano (decide (0 ∈ A)) (decide (1 ∈ A)) (decide (2 ∈ A)) (decide (3 ∈ A))
      (decide (4 ∈ A)) (decide (5 ∈ A)) (decide (6 ∈ A)) with
    ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ <;>
    rw [decide_eq_decide] at h1 h2
  · exact line_contra A 0 1 2 _ _ (hC (lv 0)) (hl 0) (hC (rv 0)) (hr 0) h1 h2
  · exact line_contra A 0 3 4 _ _ (hC (lv 1)) (hl 1) (hC (rv 1)) (hr 1) h1 h2
  · exact line_contra A 0 5 6 _ _ (hC (lv 2)) (hl 2) (hC (rv 2)) (hr 2) h1 h2
  · exact line_contra A 1 3 5 _ _ (hC (lv 3)) (hl 3) (hC (rv 3)) (hr 3) h1 h2
  · exact line_contra A 1 4 6 _ _ (hC (lv 4)) (hl 4) (hC (rv 4)) (hr 4) h1 h2
  · exact line_contra A 2 3 6 _ _ (hC (lv 5)) (hl 5) (hC (rv 5)) (hr 5) h1 h2
  · exact line_contra A 2 4 5 _ _ (hC (lv 6)) (hl 6) (hC (rv 6)) (hr 6) h1 h2

lemma three_lt : 3 < G.listChromaticNumber := by
  unfold SimpleGraph.listChromaticNumber
  by_contra hlt
  have hle := not_lt.mp hlt
  have hne : {k : ℕ | G.IsKChoosable k}.Nonempty := ⟨14, choosable_14 G⟩
  have hmem : G.IsKChoosable (sInf {k : ℕ | G.IsKChoosable k}) := Nat.sInf_mem hne
  exact not_choosable_3 (choosable_mono hmem hle)

end OMA.Erdos629H1

theorem OMA.solution : OMA.R_Erdos629_erdos_629_variants_n_three_R1.H1 :=
  Erdos629.n_le OMA.Erdos629H1.G OMA.Erdos629H1.colorable OMA.Erdos629H1.three_lt
