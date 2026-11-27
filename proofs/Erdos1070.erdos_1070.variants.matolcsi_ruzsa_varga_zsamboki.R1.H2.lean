import OMAReductions.R_Erdos1070_erdos_1070_variants_matolcsi_ruzsa_varga_zsamboki_R1

-- Step Erdos1070.erdos_1070.variants.matolcsi_ruzsa_varga_zsamboki.R1.H2
-- Credit: @GiridhariPradeep

open SimpleGraph

namespace OMA.Sol1070

/-- No two distinct points of `T` are at distance one. -/
def UF (T : Finset (EuclideanSpace ℝ (Fin 2))) : Prop := ∀ x ∈ T, ∀ y ∈ T, x ≠ y → dist x y ≠ 1

lemma card_le_alpha (Z T : Finset (EuclideanSpace ℝ (Fin 2))) (hTZ : T ⊆ Z) (hT : UF T) :
    T.card ≤ (UnitDistancePlaneGraph (Z : Set (EuclideanSpace ℝ (Fin 2)))).indepNum := by
  classical
  let s : Finset (Z : Set (EuclideanSpace ℝ (Fin 2))) := T.subtype (· ∈ (Z : Set (EuclideanSpace ℝ (Fin 2))))
  have hs : s.card = T.card := by
    simp only [s, Finset.card_subtype]
    rw [Finset.filter_true_of_mem]
    intro x hx
    exact Finset.mem_coe.mpr (hTZ hx)
  rw [← hs]
  apply IsIndepSet.card_le_indepNum
  intro u hu w hw hne hadj
  have hu' : u.1 ∈ T := Finset.mem_subtype.mp hu
  have hw' : w.1 ∈ T := Finset.mem_subtype.mp hw
  exact hT u.1 hu' w.1 hw' (fun h => hne (Subtype.ext h)) hadj

lemma exists_alpha (Z : Finset (EuclideanSpace ℝ (Fin 2))) :
    ∃ T ⊆ Z, UF T ∧ T.card = (UnitDistancePlaneGraph (Z : Set (EuclideanSpace ℝ (Fin 2)))).indepNum := by
  classical
  obtain ⟨s, hs⟩ := (UnitDistancePlaneGraph (Z : Set (EuclideanSpace ℝ (Fin 2)))).exists_isNIndepSet_indepNum
  refine ⟨s.map (Function.Embedding.subtype _), ?_, ?_, ?_⟩
  · intro x hx
    obtain ⟨u, -, rfl⟩ := Finset.mem_map.mp hx
    exact Finset.mem_coe.mp u.2
  · intro x hx y hy hne
    obtain ⟨u, hu, rfl⟩ := Finset.mem_map.mp hx
    obtain ⟨w, hw, rfl⟩ := Finset.mem_map.mp hy
    have huw : u ≠ w := fun h => hne (by rw [h])
    exact hs.isIndepSet hu hw huw
  · rw [Finset.card_map, hs.card_eq]

lemma exists_card (n : ℕ) : ∃ X : Finset (EuclideanSpace ℝ (Fin 2)), X.card = n := by
  classical
  let φ : ℕ → (EuclideanSpace ℝ (Fin 2)) := fun t => !₂[(t : ℝ), 0]
  have hφ : Function.Injective φ := by
    intro a b h
    have := congrArg (fun p : (EuclideanSpace ℝ (Fin 2)) => p 0) h
    simp [φ] at this
    exact_mod_cast this
  exact ⟨(Finset.range n).image φ, by rw [Finset.card_image_of_injective _ hφ, Finset.card_range]⟩

lemma exists_min (n : ℕ) : ∃ X : Finset (EuclideanSpace ℝ (Fin 2)), X.card = n ∧
    (UnitDistancePlaneGraph (X : Set (EuclideanSpace ℝ (Fin 2)))).indepNum ≤ Erdos1070.f n := by
  by_contra h
  have hS : ∀ X : Finset (EuclideanSpace ℝ (Fin 2)), X.card = n →
      Erdos1070.f n + 1 ≤ (UnitDistancePlaneGraph (X : Set (EuclideanSpace ℝ (Fin 2)))).indepNum := by
    intro X hX
    by_contra h'
    exact h ⟨X, hX, by omega⟩
  obtain ⟨X0, hX0⟩ := exists_card n
  have hbdd : BddAbove {m : ℕ | ∀ X : Finset (EuclideanSpace ℝ (Fin 2)), X.card = n →
      m ≤ (UnitDistancePlaneGraph (X : Set (EuclideanSpace ℝ (Fin 2)))).indepNum} :=
    ⟨(UnitDistancePlaneGraph (X0 : Set (EuclideanSpace ℝ (Fin 2)))).indepNum, fun m hm => hm X0 hX0⟩
  have := le_csSup hbdd hS
  unfold Erdos1070.f at this
  omega

lemma norm_le_sum (X : Finset (EuclideanSpace ℝ (Fin 2))) {x : (EuclideanSpace ℝ (Fin 2))} (hx : x ∈ X) : ‖x‖ ≤ ∑ z ∈ X, ‖z‖ :=
  Finset.single_le_sum (f := fun z => ‖z‖) (fun z _ => norm_nonneg z) hx

end OMA.Sol1070

open OMA.Sol1070 in
theorem OMA.solution :
    OMA.R_Erdos1070_erdos_1070_variants_matolcsi_ruzsa_varga_zsamboki_R1.H2 := by
  classical
  intro a b
  obtain ⟨Xa, hXa, hαa⟩ := exists_min a
  obtain ⟨Xb, hXb, hαb⟩ := exists_min b
  set R : ℝ := 1 + ∑ z ∈ Xa, ‖z‖ + ∑ z ∈ Xb, ‖z‖ with hR
  have hRa : 0 ≤ ∑ z ∈ Xa, ‖z‖ := Finset.sum_nonneg fun z _ => norm_nonneg z
  have hRb : 0 ≤ ∑ z ∈ Xb, ‖z‖ := Finset.sum_nonneg fun z _ => norm_nonneg z
  set v : EuclideanSpace ℝ (Fin 2) := EuclideanSpace.single 0 (3 * R) with hv
  have hvn : ‖v‖ = 3 * R := by
    rw [hv, PiLp.norm_single, Real.norm_of_nonneg (by linarith)]
  have cross : ∀ x ∈ Xa, ∀ y ∈ Xb, 1 < dist x (y + v) := by
    intro x hx y hy
    have h1 := norm_le_sum Xa hx
    have h2 := norm_le_sum Xb hy
    have htri : ‖v‖ ≤ ‖(y + v) - x‖ + ‖x‖ + ‖y‖ := by
      have : v = ((y + v) - x) + x - y := by abel
      calc ‖v‖ = ‖((y + v) - x) + x - y‖ := by rw [← this]
        _ ≤ ‖((y + v) - x) + x‖ + ‖y‖ := norm_sub_le _ _
        _ ≤ ‖(y + v) - x‖ + ‖x‖ + ‖y‖ := by gcongr; exact norm_add_le _ _
    rw [_root_.dist_comm, _root_.dist_eq_norm]
    linarith
  set Y := Xb.image (· + v) with hY
  have hYc : Y.card = b := by
    rw [hY, Finset.card_image_of_injective _ (add_left_injective v), hXb]
  have hdisj : Disjoint Xa Y := by
    rw [Finset.disjoint_left]
    intro x hx hxY
    obtain ⟨y, hy, rfl⟩ := Finset.mem_image.mp hxY
    have := cross _ hx y hy
    rw [_root_.dist_self] at this
    linarith
  set Z := Xa ∪ Y with hZ
  have hZc : Z.card = a + b := by
    rw [hZ, Finset.card_union_of_disjoint hdisj, hXa, hYc]
  have hf := Erdos1070.f_le Z
  rw [hZc] at hf
  obtain ⟨T, hTZ, hTU, hTc⟩ := exists_alpha Z
  have hsplit : T.card ≤ (T.filter (· ∈ Xa)).card + (T.filter (· ∈ Y)).card := by
    have : T = T.filter (· ∈ Xa) ∪ T.filter (· ∈ Y) := by
      ext x
      simp only [Finset.mem_union, Finset.mem_filter]
      constructor
      · intro hx
        rcases Finset.mem_union.mp (hTZ hx) with h | h
        · exact Or.inl ⟨hx, h⟩
        · exact Or.inr ⟨hx, h⟩
      · rintro (⟨hx, -⟩ | ⟨hx, -⟩) <;> exact hx
    calc T.card = (T.filter (· ∈ Xa) ∪ T.filter (· ∈ Y)).card := by rw [← this]
      _ ≤ _ := Finset.card_union_le _ _
  have hA : (T.filter (· ∈ Xa)).card ≤ Erdos1070.f a := by
    refine le_trans (card_le_alpha Xa _ ?_ ?_) hαa
    · intro x hx
      exact (Finset.mem_filter.mp hx).2
    · intro x hx y hy hne
      exact hTU x (Finset.mem_filter.mp hx).1 y (Finset.mem_filter.mp hy).1 hne
  have hB : (T.filter (· ∈ Y)).card ≤ Erdos1070.f b := by
    set T2 := (T.filter (· ∈ Y)).image (· - v) with hT2
    have hc : T2.card = (T.filter (· ∈ Y)).card :=
      Finset.card_image_of_injective _ (sub_left_injective)
    rw [← hc]
    refine le_trans (card_le_alpha Xb _ ?_ ?_) hαb
    · intro z hz
      obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp hz
      obtain ⟨y, hy, rfl⟩ := Finset.mem_image.mp (Finset.mem_filter.mp hx).2
      simpa using hy
    · intro z hz w hw hne
      obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp hz
      obtain ⟨y, hy, rfl⟩ := Finset.mem_image.mp hw
      have hxy : x ≠ y := fun h => hne (by rw [h])
      rw [_root_.dist_sub_right]
      exact hTU x (Finset.mem_filter.mp hx).1 y (Finset.mem_filter.mp hy).1 hxy
  omega
