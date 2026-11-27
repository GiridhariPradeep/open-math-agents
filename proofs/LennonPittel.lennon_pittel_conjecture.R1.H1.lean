import OMAReductions.R_LennonPittel_lennon_pittel_conjecture_R1

-- Step LennonPittel.lennon_pittel_conjecture.R1.H1: existence of a stable matching
-- (men-proposing deferred acceptance, as a well-founded descent).
-- Credit: @GiridhariPradeep

namespace OMA.SolGS

open StableMarriage

variable {n : ℕ} (p : Profile n)

/-- The woman man `m` currently proposes to: the one at rank `s m` on his list. -/
def prop (s : Fin n → ℕ) (m : Fin n) : Fin n :=
  (p.manRank m).symm ⟨s m % n, Nat.mod_lt _ m.pos⟩

/-- Every woman a man has passed over holds a proposal from someone she prefers to him. -/
def Inv (s : Fin n → ℕ) : Prop :=
  ∀ m v, ((p.manRank m v : Fin n) : ℕ) < s m →
    ∃ m', prop p s m' = v ∧ p.womanRank v m' < p.womanRank v m

lemma bound {s : Fin n → ℕ} (hI : Inv p s) (m : Fin n) : s m < n := by
  classical
  by_contra hge
  rw [not_lt] at hge
  have hall : ∀ v, ∃ m', prop p s m' = v ∧ p.womanRank v m' < p.womanRank v m :=
    fun v => hI m v (lt_of_lt_of_le (p.manRank m v).isLt hge)
  choose f hf using hall
  have hinj : Function.Injective f := by
    intro v v' h
    rw [← (hf v).1, ← (hf v').1, h]
  have hne : ∀ v, f v ≠ m := fun v h => by
    have := (hf v).2
    rw [h] at this
    exact lt_irrefl _ this
  let g : Fin n → {x : Fin n // x ≠ m} := fun v => ⟨f v, hne v⟩
  have hg : Function.Injective g := fun v v' h => hinj (congrArg Subtype.val h)
  have := Fintype.card_le_of_injective g hg
  rw [Fintype.card_subtype_compl, Fintype.card_fin, Fintype.card_unique] at this
  have hpos := m.pos
  omega

lemma prop_rank {s : Fin n → ℕ} (hI : Inv p s) (m : Fin n) :
    ((p.manRank m (prop p s m) : Fin n) : ℕ) = s m := by
  simp only [prop, Equiv.apply_symm_apply]
  exact Nat.mod_eq_of_lt (bound p hI m)

lemma stable_of_inj {s : Fin n → ℕ} (hI : Inv p s) (hinj : Function.Injective (prop p s)) :
    ∃ μ : Matching n, IsStable p μ := by
  have hbij : Function.Bijective (prop p s) := Finite.injective_iff_bijective.mp hinj
  let μ : Matching n := Equiv.ofBijective _ hbij
  refine ⟨μ, ?_⟩
  rintro m w ⟨-, hm, hw⟩
  have hm' : ((p.manRank m w : Fin n) : ℕ) < s m := by
    have := prop_rank p hI m
    have h2 : (p.manRank m w : ℕ) < (p.manRank m (μ m) : ℕ) := hm
    simp only [μ, Equiv.ofBijective_apply] at h2
    omega
  obtain ⟨m', hm'w, hlt⟩ := hI m w hm'
  have hsymm : μ.symm w = m' := by
    rw [Equiv.symm_apply_eq]
    simp only [μ, Equiv.ofBijective_apply]
    exact hm'w.symm
  rw [hsymm] at hw
  exact lt_asymm hw hlt

lemma step {s : Fin n → ℕ} (hI : Inv p s) {m₁ m₂ : Fin n} (hne : m₁ ≠ m₂)
    (heq : prop p s m₁ = prop p s m₂)
    (hpref : p.womanRank (prop p s m₂) m₁ < p.womanRank (prop p s m₂) m₂) :
    Inv p (Function.update s m₂ (s m₂ + 1)) := by
  classical
  set w := prop p s m₂ with hw
  set s' := Function.update s m₂ (s m₂ + 1) with hs'
  have hprop : ∀ m, m ≠ m₂ → prop p s' m = prop p s m := by
    intro m hm
    simp only [prop, hs', Function.update_of_ne hm]
  intro m v hv
  by_cases hm : m = m₂
  · subst m
    rw [hs', Function.update_self] at hv
    rcases Nat.lt_succ_iff_lt_or_eq.mp hv with hv | hv
    · obtain ⟨m', hm'v, hlt⟩ := hI m₂ v hv
      have hm'ne : m' ≠ m₂ := by
        rintro rfl; exact lt_irrefl _ hlt
      exact ⟨m', by rw [hprop m' hm'ne]; exact hm'v, hlt⟩
    · have hvw : v = w := by
        rw [hw]
        apply (p.manRank m₂).injective
        apply Fin.ext
        rw [prop_rank p hI m₂]
        exact hv
      subst v
      exact ⟨m₁, by rw [hprop m₁ hne]; exact heq, hpref⟩
  · have hv' : ((p.manRank m v : Fin n) : ℕ) < s m := by
      rw [hs', Function.update_of_ne hm] at hv; exact hv
    obtain ⟨m', hm'v, hlt⟩ := hI m v hv'
    by_cases hm' : m' = m₂
    · subst m'
      have hvw : v = w := hm'v.symm
      subst v
      exact ⟨m₁, by rw [hprop m₁ hne]; exact heq, lt_trans hpref hlt⟩
    · exact ⟨m', by rw [hprop m' hm']; exact hm'v, hlt⟩

lemma exists_stable_aux : ∀ (k : ℕ) (s : Fin n → ℕ), Inv p s →
    ∑ m, (n - s m) = k → ∃ μ : Matching n, IsStable p μ := by
  classical
  intro k
  induction k using Nat.strong_induction_on with
  | _ k ih =>
    intro s hI hk
    by_cases hinj : Function.Injective (prop p s)
    · exact stable_of_inj p hI hinj
    · simp only [Function.Injective, not_forall] at hinj
      obtain ⟨a, b, hab, hne⟩ := hinj
      have hrank : p.womanRank (prop p s b) a ≠ p.womanRank (prop p s b) b :=
        fun h => hne ((p.womanRank _).injective h)
      -- the woman keeps her favourite; the other proposer moves on
      have key : ∀ m₁ m₂ : Fin n, m₁ ≠ m₂ → prop p s m₁ = prop p s m₂ →
          p.womanRank (prop p s m₂) m₁ < p.womanRank (prop p s m₂) m₂ →
          ∃ μ : Matching n, IsStable p μ := by
        intro m₁ m₂ hne' heq hpref
        have hI' := step p hI hne' heq hpref
        have hb := bound p hI m₂
        refine ih (∑ m, (n - Function.update s m₂ (s m₂ + 1) m)) ?_ _ hI' rfl
        rw [← hk]
        apply Finset.sum_lt_sum
        · intro m _
          by_cases h : m = m₂
          · subst h; rw [Function.update_self]; omega
          · rw [Function.update_of_ne h]
        · exact ⟨m₂, Finset.mem_univ _, by rw [Function.update_self]; omega⟩
      rcases lt_or_gt_of_ne hrank with h | h
      · exact key a b hne hab h
      · exact key b a (Ne.symm hne) hab.symm (by rw [hab]; exact h)

end OMA.SolGS

theorem OMA.solution : OMA.R_LennonPittel_lennon_pittel_conjecture_R1.H1 := by
  classical
  intro n p
  have hI : OMA.SolGS.Inv p (fun _ => 0) := by
    intro m v hv
    exact absurd hv (Nat.not_lt_zero _)
  obtain ⟨μ, hμ⟩ := OMA.SolGS.exists_stable_aux p _ _ hI rfl
  unfold StableMarriage.numStableMatchings
  exact Fintype.card_pos_iff.mpr ⟨⟨μ, hμ⟩⟩
